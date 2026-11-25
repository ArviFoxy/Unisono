/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.OrderedView
public import Unisono.Solutions.Controller.BuiltLate
public import Unisono.Spec.Models.GenerativeUndisturbed

/-!
# What a host's view holds while nothing disturbs the stream

In a world built from a regular draw, take the controller with any rules
whose capture schedule is that of the knots, and a period from the true
time `a₀` to `b₀` in which the path from the sender to the host of a
speaker is idle (`Draw.PathIdle`). `streamDelay` is the least delay of that
path, and `World.lastCapture w b` is the true time at which the last frame
of capture block `b` is captured.

At a request that the host handles by `b₀`:

* `mem_arrivalsOf_of_idle`: every arrival in the host's view at which its
  clock read more than at the least delay after `a₀` is that of a block
  whose last frame was captured after `a₀`: the pair of the host's reading
  the least delay after that capture and of the sender's reading at the
  capture.
* `arrival_mem_arrivalsOf_of_idle`: every block whose last frame was
  captured from `a₀` on, and at least the least delay before the request,
  has that pair among the arrivals of the view.
* `arrivalsOf_request_pairwise`: the arrivals of the view are in the order
  of the host's readings.
* `arrivalSlope_of_undisturbed`: when the rates of the two hosts' clocks
  stay within their bands (`Draw.Undisturbed`), and two blocks finished in
  the period have arrived whose arrivals are at least `baseline` apart on
  the host's clock, the slope that the host takes lies between the least
  rate of the sender's clock divided by the largest rate of the host's
  clock and the largest divided by the least, provided those two numbers
  are within `slopeBound` of one.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The true time at which the last frame of capture block `b` is
captured. -/
def World.lastCapture (w : World H R) (b : ℕ) : Time :=
  w.source.capture (w.source.first (b + 1) - 1)

end Unisono.Spec

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld Unisono.Model.Descent

variable {H : Type} {R : ℕ}

/-- The least delay of the stream to speaker `r`: of a message from the
sender to the speaker's host. -/
def streamDelay (f : Member H R) (d : Draw H R) (w : World H R) (r : Fin R) : ℝ :=
  d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r)

/-- The least delay of a clock query of the host of speaker `r`: of a
message from that host to the sender. -/
def queryDelay (f : Member H R) (d : Draw H R) (w : World H R) (r : Fin R) : ℝ :=
  d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender

/-- The least delay of the stream is positive in a regular draw. -/
theorem streamDelay_pos {d : Draw H R} (hd : d.Regular) (f : Member H R) (w : World H R)
    (r : Fin R) : 0 < streamDelay f d w r :=
  hd.leastDelay_pos f _ _

/-- The least delay of a clock query is positive in a regular draw. -/
theorem queryDelay_pos {d : Draw H R} (hd : d.Regular) (f : Member H R) (w : World H R)
    (r : Fin R) : 0 < queryDelay f d w r :=
  hd.leastDelay_pos f _ _

/-- The least delays of a clock query and of the stream add up to the least
round trip between the two hosts. -/
theorem queryDelay_add_streamDelay {d : Draw H R} (hd : d.Regular) (f : Member H R)
    (w : World H R) (r : Fin R) :
    queryDelay f d w r + streamDelay f d w r = f.roundTrip (w.host r) w.sender :=
  hd.leastDelay_add f _ _

variable [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R} {p : FixedDelay.Params H} {rules : Rules H R} {q : LevelSettings}
  {share : ℝ} {kn : KnotSettings}

/-- **A recent arrival in the view is that of a block finished in the idle
period.** In a world built from a regular draw, in the setting
`KnotSetting`, let the path from the sender to the host of speaker `r` be
idle from `a₀` to `b₀`, and let step `n` handle a request of the speaker by
`b₀`. Every arrival in the host's view at which its clock read more than at
the least delay after `a₀` is, for some block `b` whose last frame was
captured after `a₀`: the reading of the host's clock the least delay after
that capture, and the reading of the sender's clock at the capture. The
sender's host handled the handover at the capture, and the block arrived
before the request. -/
theorem mem_arrivalsOf_of_idle (hB : m.Builds f d w) (hd : d.Regular)
    (hK : KnotSetting p rules w (d.arrival f) q share kn) (lookahead : ℕ+) {r : Fin R}
    {a₀ b₀ : Time} (hidle : d.PathIdle w.sender (w.host r) a₀ b₀) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀) {a : ℝ × ℝ}
    (ha : a ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
      (w.host r) ++ [w.askedEvent r β]))
    (hrecent : (w.clock (w.host r)).read (a₀ + streamDelay f d w r) < a.1) :
    ∃ b, a₀ < w.lastCapture b
      ∧ w.lastCapture b + streamDelay f d w r < (w.speaker r).asked β
      ∧ w.source.handed b = w.lastCapture b
      ∧ a = ((w.clock (w.host r)).read (w.lastCapture b + streamDelay f d w r),
            (w.clock w.sender).read (w.lastCapture b)) := by
  have happ : arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
      (w.host r) ++ [w.askedEvent r β])
      = arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := arrivalsOf_append_asked _ _ _ _ _
  rw [happ] at ha
  obtain ⟨b, rfl, hb⟩ := mem_arrivalsOf_noLoss hK.capture hK.noLoss lookahead ha
  have hnext := (ruled p rules : Solution H R Payload).askedNext_of_earliest w lookahead hE
  have hlt := hb r
  rw [hnext] at hlt
  have hrec : a₀ + streamDelay f d w r
      < d.arrival f w.sender (w.host r) (w.source.handed b) :=
    (w.clock (w.host r)).strictMono.lt_iff_lt.mp hrecent
  obtain ⟨h1, h2, h3⟩ := hB.block_of_lt_arrival (hd.linkPaused_monotone _ _)
    (hd.hostPaused_monotone _) (hd.hostPaused_monotone _) hidle
    (hd.leastDelay_pos f _ _).le hrec (hlt.le.trans hβ)
  refine ⟨b, h1, ?_, h2, ?_⟩
  · rw [h3] at hlt
    exact hlt
  · refine Prod.ext ?_ ?_
    · show (w.clock (w.host r)).read (d.arrival f w.sender (w.host r) (w.source.handed b)) = _
      rw [h3]
      rfl
    · show (w.clock w.sender).read (w.source.handed b) = _
      rw [h2]
      rfl

/-- **A block finished in the idle period, early enough, is among the
arrivals of the view.** In the setting of `mem_arrivalsOf_of_idle`, for a
speaker on a host other than the sender's, let the last frame of block `b`
be captured from `a₀` on and more than the least delay before the request.
Then the host's view holds the pair of the reading of its clock the least
delay after that capture and of the reading of the sender's clock at the
capture. -/
theorem arrival_mem_arrivalsOf_of_idle (hB : m.Builds f d w) (hd : d.Regular)
    (hK : KnotSetting p rules w (d.arrival f) q share kn) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) {a₀ b₀ : Time}
    (hidle : d.PathIdle w.sender (w.host r) a₀ b₀) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀) {b : ℕ} (hb₁ : a₀ ≤ w.lastCapture b)
    (hb₂ : w.lastCapture b + streamDelay f d w r < (w.speaker r).asked β) :
    ((w.clock (w.host r)).read (w.lastCapture b + streamDelay f d w r),
        (w.clock w.sender).read (w.lastCapture b))
      ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r) ++ [w.askedEvent r β]) := by
  have happ : arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
      (w.host r) ++ [w.askedEvent r β])
      = arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := arrivalsOf_append_asked _ _ _ _ _
  rw [happ]
  obtain ⟨h1, h2⟩ := hB.arrival_of_captured (hd.linkPaused_monotone _ _)
    (hd.hostPaused_monotone _) (hd.hostPaused_monotone _) hidle
    (hd.leastDelay_pos f _ _).le hb₁ (hb₂.le.trans hβ)
  have htime : (ruled p rules : Solution H R Payload).eventTime w lookahead n
      = (w.speaker r).asked β :=
    (ruled p rules : Solution H R Payload).handled_time w lookahead
      ((ruled p rules : Solution H R Payload).handled_of_asked w lookahead hE)
  have hmem := arrival_mem_arrivalsOf hK.capture hK.noLoss lookahead hr (b := b) (n := n)
    (by rw [htime, h2]; exact hb₂)
  rw [h2] at hmem
  unfold World.handedReading at hmem
  rw [h1] at hmem
  exact hmem

omit [DecidableEq H] in
/-- **The arrivals of a host's view at a request are in the order of the
host's readings**, in the run of any solution in any world. -/
theorem arrivalsOf_request_pairwise [DecidableEq H] (σ : Solution H R Payload) (w : World H R)
    (lookahead : ℕ+) {n : ℕ} {r : Fin R} {β : ℕ}
    (hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)) :
    (arrivalsOf ((σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r β])).Pairwise
      fun a a' => a.1 ≤ a'.1 :=
  arrivalsOf_pairwise (σ.requestView_pairwise w lookahead hE)

/-- **The slope that a host takes while nothing disturbs the stream.** In a
world built from a regular draw, in the setting `KnotSetting`, let the
stream to speaker `r`, on a host other than the sender's, be undisturbed
from `a₀` to `b₀` with valid bands `B`, and let step `n` handle a request of
the speaker by `b₀`. Let blocks `b₂` and `b₁` be finished after `a₀`, with
the host's readings at their arrivals at least `baseline > 0` apart, and
let `b₁` have arrived before the request. If the least rate of the sender's
clock divided by the largest rate of the host's clock, and the largest
divided by the least, are within `slopeBound` of one, then the slope that
the host takes lies between those two numbers. -/
theorem arrivalSlope_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular)
    (hK : KnotSetting p rules w (d.arrival f) q share kn) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) (t : TimingSettings) {B : RateBands} {ρ : ℝ} {a₀ b₀ : Time}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    (hbase : 0 < t.baseline) (hlo : 1 - t.slopeBound ≤ B.senderLo / B.hostHi)
    (hhi : B.senderHi / B.hostLo ≤ 1 + t.slopeBound) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀) {b₁ b₂ : ℕ} (h₂ : a₀ < w.lastCapture b₂)
    (h12 : (w.clock (w.host r)).read (w.lastCapture b₂ + streamDelay f d w r) + t.baseline
      ≤ (w.clock (w.host r)).read (w.lastCapture b₁ + streamDelay f d w r))
    (h₁ : w.lastCapture b₁ + streamDelay f d w r < (w.speaker r).asked β) :
    arrivalSlope t (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r) ++ [w.askedEvent r β])
      ∈ Set.Icc (B.senderLo / B.hostHi) (B.senderHi / B.hostLo) := by
  have hδ := streamDelay_pos hd f w r
  have hC := (w.clock (w.host r)).strictMono
  -- The two blocks are among the arrivals.
  have h21 : w.lastCapture b₂ < w.lastCapture b₁ := by
    have : (w.clock (w.host r)).read (w.lastCapture b₂ + streamDelay f d w r)
        < (w.clock (w.host r)).read (w.lastCapture b₁ + streamDelay f d w r) := by linarith
    have := hC.lt_iff_lt.mp this
    linarith
  have hc := arrival_mem_arrivalsOf_of_idle hB hd hK lookahead hr hU.forward hE hβ h₂.le
    (by linarith)
  have hN := arrival_mem_arrivalsOf_of_idle hB hd hK lookahead hr hU.forward hE hβ
    (h₂.le.trans h21.le) h₁
  obtain ⟨a, ha, a', ha', haN, hca', hbase', hsl⟩ := arrivalSlope_eq_of_pairwise t hbase
    (arrivalsOf_request_pairwise _ w lookahead hE) hc hN h12
  -- Both arrivals of the slope are those of blocks finished in the period.
  have hrec₂ : (w.clock (w.host r)).read (a₀ + streamDelay f d w r)
      < (w.clock (w.host r)).read (w.lastCapture b₂ + streamDelay f d w r) :=
    hC (by linarith)
  obtain ⟨c', hc'1, hc'2, -, rfl⟩ := mem_arrivalsOf_of_idle hB hd hK lookahead hU.forward hE hβ
    ha' (lt_of_lt_of_le hrec₂ hca')
  obtain ⟨c, hc1, hc2, -, rfl⟩ := mem_arrivalsOf_of_idle hB hd hK lookahead hU.forward hE hβ
    ha (by
      have h1 : (w.clock (w.host r)).read (a₀ + streamDelay f d w r)
          < (w.clock (w.host r)).read (w.lastCapture c' + streamDelay f d w r) :=
        lt_of_lt_of_le hrec₂ hca'
      linarith)
  dsimp only at hbase' hsl
  have hcc' : w.lastCapture c' < w.lastCapture c := by
    have : (w.clock (w.host r)).read (w.lastCapture c' + streamDelay f d w r)
        < (w.clock (w.host r)).read (w.lastCapture c + streamDelay f d w r) := by linarith
    have := hC.lt_iff_lt.mp this
    linarith
  -- The advances of the two clocks between the two blocks.
  obtain ⟨hs1, hs2⟩ := hU.sender_sub hd hc'1.le hcc'.le (by linarith)
  obtain ⟨hh1, hh2⟩ := hU.host_sub hd
    (y := w.lastCapture c' + streamDelay f d w r) (y' := w.lastCapture c + streamDelay f d w r)
    (by linarith) (by linarith) (by linarith)
  rw [← hB.clock, ← hB.clock] at hs1 hs2 hh1 hh2
  have hΔ : 0 < w.lastCapture c - w.lastCapture c' := by linarith
  have e : w.lastCapture c + streamDelay f d w r - (w.lastCapture c' + streamDelay f d w r)
      = w.lastCapture c - w.lastCapture c' := by ring
  rw [e] at hh1 hh2
  have hden : 0 < (w.clock (w.host r)).read (w.lastCapture c + streamDelay f d w r)
      - (w.clock (w.host r)).read (w.lastCapture c' + streamDelay f d w r) := by
    have := mul_pos hBv.host_pos hΔ
    linarith
  have hhostHi : 0 < B.hostHi := lt_of_lt_of_le hBv.host_pos hBv.host_le
  have hraw1 : B.senderLo / B.hostHi
      ≤ ((w.clock w.sender).read (w.lastCapture c) - (w.clock w.sender).read (w.lastCapture c'))
        / ((w.clock (w.host r)).read (w.lastCapture c + streamDelay f d w r)
          - (w.clock (w.host r)).read (w.lastCapture c' + streamDelay f d w r)) := by
    rw [le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hhostHi]
    have h1 := mul_le_mul_of_nonneg_left hh2 hBv.sender_pos.le
    have h2 := mul_le_mul_of_nonneg_right hs1 hhostHi.le
    nlinarith
  have hraw2 : ((w.clock w.sender).read (w.lastCapture c)
        - (w.clock w.sender).read (w.lastCapture c'))
        / ((w.clock (w.host r)).read (w.lastCapture c + streamDelay f d w r)
          - (w.clock (w.host r)).read (w.lastCapture c' + streamDelay f d w r))
      ≤ B.senderHi / B.hostLo := by
    rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hBv.host_pos]
    have hsHi : 0 ≤ B.senderHi := hBv.sender_pos.le.trans hBv.sender_le
    have h1 := mul_le_mul_of_nonneg_left hh1 hsHi
    have h2 := mul_le_mul_of_nonneg_right hs2 hBv.host_pos.le
    nlinarith
  rw [hsl]
  unfold clampTo
  rw [min_eq_right (hraw2.trans hhi), max_eq_right (hlo.trans hraw1)]
  exact ⟨hraw1, hraw2⟩

end Unisono.Solutions.Controller
