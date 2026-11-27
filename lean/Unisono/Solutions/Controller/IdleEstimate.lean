/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.IdleExchanges
public import Unisono.Solutions.Controller.IdleRequests

/-!
# A host's estimate of the sender's clock while nothing disturbs the stream

In a world built from a regular draw, let the stream to a speaker be
undisturbed from the true time `a₀` to `b₀` (`Draw.Undisturbed`) with the
rates of the four clocks within the bands `B`.

* `drift_mem_of_undisturbed`: over a part of the stretch, the sender's clock
  runs ahead of a line whose slope lies between the least rate of the
  sender's clock divided by the largest rate of the host's clock and the
  largest divided by the least by at most `B.driftUp` per second, and falls
  behind it by at most `B.driftDown` per second.
* `windowArrival_of_undisturbed`: when the stretch began more than `window`
  before a request, on the host's clock and after the least delay, every
  arrival that the estimate uses at the request is that of a block finished
  in the stretch, which took the least delay.
* `RequestHistory`: what the estimate at the request of block `β + 1` needs
  from the time since `a₀`: an earlier request, arrivals for the window and
  for the slope, and a clock query sent and answered.
* `BandsFit`: the conditions on the settings: the slope and the ratio are
  not cut by `slopeBound`, and `intervalSlack` covers what the bands allow.
* `envelopeReading_of_undisturbed`: **the estimate while nothing disturbs
  the stream.** With `RequestHistory` and `BandsFit`, for an output sample
  that leaves in the stretch: the host has an estimate from the arrivals,
  the interval check holds, and the reading of the sender's clock when the
  output sample leaves minus the estimate lies between `estimateLow` and
  `estimateHigh`. Both are close to the least delay of the stream on the
  sender's clock minus half of the least round trip on the host's clock,
  which is the error that no clock exchange shows.

Not proved here: the block check, and so that the host keeps the estimate.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld Unisono.Model.Descent

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} {p : FixedDelay.Params H} {rules : Rules H R}
  {q : LevelSettings} {share : ℝ} {kn : KnotSettings} {B : RateBands} {ρ : ℝ}
  {a₀ b₀ : Time}

omit [DecidableEq H] in
/-- **The drift of the sender's clock against a host's slope while nothing
disturbs the stream.** Over a part of an undisturbed stretch, for a slope
between the least rate of the sender's clock divided by the largest rate of
the host's clock and the largest divided by the least: the sender's clock
falls behind the line of that slope by at most `B.driftDown` times the
length of the part, and runs ahead of it by at most `B.driftUp` times the
length. -/
theorem drift_mem_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid) {sl : ℝ}
    (hsl : sl ∈ Set.Icc (B.senderLo / B.hostHi) (B.senderHi / B.hostLo)) {x y : Time}
    (hax : a₀ ≤ x) (hxy : x ≤ y) (hyb : y ≤ b₀) :
    -(B.driftDown * (y - x)) ≤ w.drift (w.host r) sl x y
      ∧ w.drift (w.host r) sl x y ≤ B.driftUp * (y - x) := by
  obtain ⟨hs1, hs2⟩ := hU.sender_sub hd hax hxy hyb
  obtain ⟨hh1, hh2⟩ := hU.host_sub hd hax hxy hyb
  rw [← hB.clock, ← hB.clock] at hs1 hs2 hh1 hh2
  have hL : 0 ≤ y - x := by linarith
  have hHi : 0 < B.hostHi := lt_of_lt_of_le hBv.host_pos hBv.host_le
  have hslpos : 0 ≤ sl := (div_nonneg hBv.sender_pos.le hHi.le).trans hsl.1
  have hC0 : 0 ≤ (w.clock (w.host r)).read y - (w.clock (w.host r)).read x :=
    (mul_nonneg hBv.host_pos.le hL).trans hh1
  have h1 : B.senderLo / B.hostHi * (B.hostLo * (y - x))
      ≤ sl * ((w.clock (w.host r)).read y - (w.clock (w.host r)).read x) :=
    mul_le_mul hsl.1 hh1 (mul_nonneg hBv.host_pos.le hL) hslpos
  have h2 : sl * ((w.clock (w.host r)).read y - (w.clock (w.host r)).read x)
      ≤ B.senderHi / B.hostLo * (B.hostHi * (y - x)) :=
    mul_le_mul hsl.2 hh2 hC0
      (div_nonneg (hBv.sender_pos.le.trans hBv.sender_le) hBv.host_pos.le)
  have e1 : B.driftUp * (y - x)
      = B.senderHi * (y - x) - B.senderLo / B.hostHi * (B.hostLo * (y - x)) := by
    unfold RateBands.driftUp
    ring
  have e2 : B.driftDown * (y - x)
      = B.senderHi / B.hostLo * (B.hostHi * (y - x)) - B.senderLo * (y - x) := by
    unfold RateBands.driftDown
    ring
  rw [e1, e2]
  unfold World.drift
  constructor <;> linarith

/-- **The arrivals that the estimate uses while nothing disturbs the
stream.** In a world built from a regular draw, in the setting
`KnotSetting`, let the path from the sender to the host of speaker `r`, a
host other than the sender's, be idle from `a₀` to `b₀`, and let step `n`
handle a request of the speaker by `b₀`. Let the host's clock have advanced
by more than `window` from the least delay after `a₀` to the request, and
let block `bw` be finished from `a₀` on and arrive within `window` before
the request. Then the arrival of `bw` is one that the estimate uses, and
every arrival that the estimate uses is that of a block whose last frame
was captured after `a₀`, which arrived the least delay later, within
`window` before the request on the host's clock. -/
theorem windowArrival_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular)
    (hK : KnotSetting p rules w (d.arrival f) q share kn) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) (t : TimingSettings)
    (hidle : d.PathIdle w.sender (w.host r) a₀ b₀) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀)
    (hwin : (w.clock (w.host r)).read (a₀ + streamDelay f d w r) + t.window
      < (w.clock (w.host r)).read ((w.speaker r).asked β))
    {bw : ℕ} (hbw₁ : a₀ ≤ w.lastCapture bw)
    (hbw₂ : w.lastCapture bw + streamDelay f d w r < (w.speaker r).asked β)
    (hbw₃ : (w.clock (w.host r)).read ((w.speaker r).asked β) - t.window
      ≤ (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r)) :
    ((w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r),
          (w.clock w.sender).read (w.lastCapture bw))
        ∈ windowArrivals t (((ruled p rules : Solution H R Payload).states w lookahead n).views
          (w.host r) ++ [w.askedEvent r β])
      ∧ ∀ a ∈ windowArrivals t (((ruled p rules : Solution H R Payload).states w lookahead
            n).views (w.host r) ++ [w.askedEvent r β]),
          ∃ b, a₀ < w.lastCapture b
            ∧ w.lastCapture b + streamDelay f d w r < (w.speaker r).asked β
            ∧ (w.clock (w.host r)).read ((w.speaker r).asked β) - t.window
              ≤ (w.clock (w.host r)).read (w.lastCapture b + streamDelay f d w r)
            ∧ a = ((w.clock (w.host r)).read (w.lastCapture b + streamDelay f d w r),
                  (w.clock w.sender).read (w.lastCapture b)) := by
  have h₁ := arrival_mem_arrivalsOf_of_idle hB hd hK lookahead hr hidle hE hβ hbw₁ hbw₂
  have hrd : (w.askedEvent r β : Event H R Payload).reading
      = (w.clock (w.host r)).read ((w.speaker r).asked β) := rfl
  have hw : (w.askedEvent r β : Event H R Payload).reading - t.window
      ≤ ((w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r),
          (w.clock w.sender).read (w.lastCapture bw)).1 := by
    rw [hrd]
    exact hbw₃
  refine ⟨(mem_windowArrivals_iff t h₁ hw).mpr ⟨h₁, hw⟩, fun a ha => ?_⟩
  obtain ⟨ha₁, ha₂⟩ := (mem_windowArrivals_iff t h₁ hw).mp ha
  rw [hrd] at ha₂
  obtain ⟨b, hb1, hb2, -, rfl⟩ := mem_arrivalsOf_of_idle hB hd hK lookahead hidle hE hβ ha₁
    (by linarith)
  exact ⟨b, hb1, hb2, ha₂, rfl⟩

/-- **What the estimate at the request of block `β + 1` of speaker `r` needs
from the time since `a₀`.**

* The host handled the request of block `β` after `a₀`.
* The host's clock advanced by more than `window` from the least delay
  after `a₀` to the request, and some block finished from `a₀` on arrived
  within `window` before the request.
* Two blocks finished after `a₀` arrived before the request, at least
  `baseline` apart on the host's clock.
* The host's clock advanced by more than `exchangeWindow` from `a₀` to the
  request. For some true time `T` from `a₀` on, at most `exchangeWindow`
  before the request on the host's clock, the host handled a request `β₁`
  at least the polling period after `T` on its clock, and more than the
  least round trip before the request of block `β + 1`. -/
structure RequestHistory (t : TimingSettings) (p : FixedDelay.Params H) (f : Member H R)
    (d : Draw H R) (w : World H R) (r : Fin R) (a₀ : Time) (β : ℕ) : Prop where
  prev : a₀ < (w.speaker r).asked β
  window : (w.clock (w.host r)).read (a₀ + streamDelay f d w r) + t.window
    < (w.clock (w.host r)).read ((w.speaker r).asked (β + 1))
  windowBlock : ∃ bw, a₀ ≤ w.lastCapture bw
    ∧ w.lastCapture bw + streamDelay f d w r < (w.speaker r).asked (β + 1)
    ∧ (w.clock (w.host r)).read ((w.speaker r).asked (β + 1)) - t.window
      ≤ (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r)
  slopeBlocks : ∃ b₁ b₂, a₀ < w.lastCapture b₂
    ∧ (w.clock (w.host r)).read (w.lastCapture b₂ + streamDelay f d w r) + t.baseline
      ≤ (w.clock (w.host r)).read (w.lastCapture b₁ + streamDelay f d w r)
    ∧ w.lastCapture b₁ + streamDelay f d w r < (w.speaker r).asked (β + 1)
  exchangeWindow : (w.clock (w.host r)).read a₀ + t.exchangeWindow
    < (w.clock (w.host r)).read ((w.speaker r).asked (β + 1))
  query : ∃ (T : Time) (β₁ : ℕ), a₀ ≤ T
    ∧ (w.clock (w.host r)).read ((w.speaker r).asked (β + 1)) - (w.clock (w.host r)).read T
      ≤ t.exchangeWindow
    ∧ (w.clock (w.host r)).read T + p.period
      ≤ (w.clock (w.host r)).read ((w.speaker r).asked β₁)
    ∧ (w.speaker r).asked β₁ + queryDelay f d w r + streamDelay f d w r
      < (w.speaker r).asked (β + 1)

/-- **The settings fit the bands**, for a least round trip `RT`: the
interval of the slope and the interval of the ratio lie within `slopeBound`
of one, so that neither is cut; and the largest rate of the sender's clock
times the round trip, plus what the sender's clock can drift against the
host's slope over the longer of `exchangeWindow` and `window` on the host's
clock, is at most the round trip in use at its least plus `intervalSlack`,
so that the interval check holds. -/
structure BandsFit (t : TimingSettings) (B : RateBands) (RT : ℝ) : Prop where
  slope_lo : 1 - t.slopeBound ≤ B.senderLo / B.hostHi
  slope_hi : B.senderHi / B.hostLo ≤ 1 + t.slopeBound
  ratio_lo : 1 - t.slopeBound ≤ B.hostLo / B.outputHi
  ratio_hi : B.hostHi / B.outputLo ≤ 1 + t.slopeBound
  interval : B.senderHi * RT
      + (B.driftUp + B.driftDown) * (max t.exchangeWindow t.window / B.hostLo)
    ≤ min (B.hostLo * RT) t.tripCap + t.intervalSlack

/-- A lower bound of the reading of the sender's clock when an output
sample leaves minus the host's estimate, while nothing disturbs the stream:
for the least delay `δ` of the stream, the least round trip `RT`, a bound
`L` of the true time from the arrival that the estimate rests on to the
output sample, and the time `D` on the device's clock from the request to
the output sample. -/
def estimateLow (B : RateBands) (δ RT L D : ℝ) : ℝ :=
  -(B.driftDown * L) + B.senderLo * δ - B.senderHi / B.hostLo * (B.ratioWidth * D)
    - B.hostHi * RT / 2

/-- An upper bound of the reading of the sender's clock when an output
sample leaves minus the host's estimate, while nothing disturbs the stream
(`estimateLow`). -/
def estimateHigh (t : TimingSettings) (B : RateBands) (δ RT L D : ℝ) : ℝ :=
  B.driftUp * L + B.senderHi * δ + B.senderHi / B.hostLo * (B.ratioWidth * D)
    - min (B.hostLo * RT) t.tripCap / 2

/-- **The estimate while nothing disturbs the stream.** In a world built
from a regular draw, in the setting `KnotSetting` with a polling period that
is not negative and the told rate and lead of the model, let the stream to
speaker `r`, on a host other than the sender's, be undisturbed from `a₀` to
`b₀` with valid bands that the settings fit (`BandsFit`). Let step `n`
handle the request of block `β + 1` by `b₀`, with the history that the
estimate needs since `a₀` (`RequestHistory`), and let output sample `k`
leave by `b₀`, at or after the request on the device's clock. Then:

* the host has an estimate `s` from the arrivals of blocks;
* the interval check holds;
* the reading of the sender's clock when the output sample leaves, minus
  `s`, lies between `estimateLow` and `estimateHigh`, for the least delay of
  the stream, the least round trip, the time `window / hostLo` plus the time
  from the request to the output sample at the device's least rate, and the
  time on the device's clock from the request to the output sample. -/
theorem envelopeReading_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular)
    (hK : KnotSetting p rules w (d.arrival f) q share kn) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) (hperiod : 0 ≤ p.period) {t : TimingSettings}
    (hrate : t.rate = m.rate) (hleadEq : t.lead = m.lead) (hbase : 0 < t.baseline)
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    (hfit : BandsFit t B (f.roundTrip (w.host r) w.sender)) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due
      = some (.asked r (β + 1)))
    (hβ : (w.speaker r).asked (β + 1) ≤ b₀) (hH : RequestHistory t p f d w r a₀ β) {k : ℕ}
    (hlead : 0 ≤ outputLead m w r (β + 1) k) (hout : (w.speaker r).out k ≤ b₀) :
    ∃ s, envelopeReading w.sender (timingParts t) (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r (β + 1)]) r k = some s
      ∧ intervalCheck t (((ruled p rules : Solution H R Payload).states w lookahead n).views
          (w.host r) ++ [w.askedEvent r (β + 1)])
      ∧ estimateLow B (streamDelay f d w r) (f.roundTrip (w.host r) w.sender)
            (t.window / B.hostLo + outputLead m w r (β + 1) k / B.outputLo)
            (outputLead m w r (β + 1) k)
          ≤ (w.clock w.sender).read ((w.speaker r).out k) - s
      ∧ (w.clock w.sender).read ((w.speaker r).out k) - s
          ≤ estimateHigh t B (streamDelay f d w r) (f.roundTrip (w.host r) w.sender)
            (t.window / B.hostLo + outputLead m w r (β + 1) k / B.outputLo)
            (outputLead m w r (β + 1) k) := by
  have hδq := queryDelay_pos hd f w r
  have hδs := streamDelay_pos hd f w r
  have hRT := queryDelay_add_streamDelay hd f w r
  have hsender := hK.noLoss.sender
  have hmono : (w.speaker r).asked β ≤ (w.speaker r).asked (β + 1) :=
    (w.speaker r).asked_mono (Nat.le_succ β)
  have hhostHi : 0 < B.hostHi := lt_of_lt_of_le hBv.host_pos hBv.host_le
  have hsendHi : 0 < B.senderHi := lt_of_lt_of_le hBv.sender_pos hBv.sender_le
  have hCmono := (w.clock (w.host r)).strictMono.monotone
  have hup := RateBands.driftUp_nonneg hBv
  have hdown := RateBands.driftDown_nonneg hBv
  have hprev := hH.prev
  -- The requests and the output sample.
  obtain ⟨hle, -, hod⟩ := out_sub_asked_mem hB hd hU hBv (lt_of_lt_of_le hprev hmono) hβ hlead
    hout
  -- The window.
  obtain ⟨bw, hbw₁, hbw₂, hbw₃⟩ := hH.windowBlock
  obtain ⟨hwmem, hwall⟩ := windowArrival_of_undisturbed hB hd hK lookahead hr t hU.forward hE
    hβ hH.window hbw₁ hbw₂ hbw₃
  -- The slope.
  obtain ⟨b₁, b₂, hs₂, hs12, hs₁⟩ := hH.slopeBlocks
  have hsl := arrivalSlope_of_undisturbed hB hd hK lookahead hr t hU hBv hbase hfit.slope_lo
    hfit.slope_hi hE hβ hs₂ hs12 hs₁
  -- The exchange.
  obtain ⟨T, β₁, hT, hTwin, hTper, hTdone⟩ := hH.query
  obtain ⟨s₁, hTs, hsβ₁, hx₀⟩ := exists_exchange_of_undisturbed hB hd hK lookahead hr hperiod
    hU hE hβ hT hTper hTdone
  have hrd : (w.askedEvent r (β + 1) : Event H R Payload).reading
      = (w.clock (w.host r)).read ((w.speaker r).asked (β + 1)) := rfl
  have hx₀rec := mem_recentExchanges.mpr ⟨w.askedEvent r (β + 1), List.getLast?_concat, hx₀,
    (by
      rw [hrd]
      show (w.clock (w.host r)).read ((w.speaker r).asked (β + 1))
        - (w.clock (w.host r)).read s₁ ≤ t.exchangeWindow
      have := hCmono hTs
      linarith)⟩
  obtain ⟨hhalf1, hhalf2⟩ := halfTrip_mem_of_undisturbed hB hd hsender lookahead t hU hBv hE hβ
    hH.exchangeWindow (List.ne_nil_of_mem hx₀rec)
  rw [hRT] at hhalf1 hhalf2
  have hout_eq := requestOutput_eq (ruled p rules : Solution H R Payload) w lookahead t hE k
  -- Name the view, the slope and half of the round trip in use.
  obtain ⟨V, hV⟩ : ∃ V, V = ((ruled p rules : Solution H R Payload).states w lookahead n).views
      (w.host r) ++ [w.askedEvent r (β + 1)] := ⟨_, rfl⟩
  rw [← hV] at hwmem hwall hsl hx₀rec hhalf1 hhalf2 hout_eq ⊢
  obtain ⟨sl, hsl_def⟩ : ∃ sl, sl = arrivalSlope t V := ⟨_, rfl⟩
  obtain ⟨hf, hf_def⟩ : ∃ hf, hf = halfTrip t V := ⟨_, rfl⟩
  rw [← hsl_def] at hsl
  rw [← hf_def] at hhalf1 hhalf2
  have hsl0 : 0 ≤ sl := (div_nonneg hBv.sender_pos.le hhostHi.le).trans hsl.1
  -- The estimate exists.
  have hWne : windowArrivals t V ≠ [] := List.ne_nil_of_mem hwmem
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    (envelope_isSome sl (outputAt t w r (β + 1) k) hWne)
  have hs : envelopeReading w.sender (timingParts t) (w.host r) V r k = some (v + hf) := by
    unfold envelopeReading
    rw [ite_eq_right hr]
    show (envelope (arrivalSlope t V) (requestOutput t V r k) (windowArrivals t V)).map
      (· + halfTrip t V) = _
    rw [hout_eq, ← hsl_def, ← hf_def, hv]
    rfl
  refine ⟨v + hf, hs, ?_, ?_⟩
  · -- The interval check, with the exchange found and the arrival of `bw`.
    obtain ⟨v₀, hv₀⟩ := Option.isSome_iff_exists.mp (envelope_isSome sl 0 hWne)
    have hv₀le := le_of_envelope hv₀ _ hwmem
    dsimp only at hv₀le
    rw [hsl_def] at hv₀
    refine ⟨_, hx₀rec, v₀, hv₀, ?_⟩
    show (w.clock w.sender).read (s₁ + queryDelay f d w r)
        - arrivalSlope t V * (w.clock (w.host r)).read s₁
      ≤ v₀ + 2 * halfTrip t V + t.intervalSlack
    rw [← hsl_def, ← hf_def]
    have hs₁b : s₁ + queryDelay f d w r + streamDelay f d w r < (w.speaker r).asked (β + 1) := by
      linarith
    -- The two legs on the sender's clock.
    obtain ⟨-, hA1⟩ := hU.sender_sub hd (y := s₁) (y' := s₁ + queryDelay f d w r)
      (hT.trans hTs) (by linarith) (by linarith)
    obtain ⟨-, hA2⟩ := hU.sender_sub hd (y := w.lastCapture bw)
      (y' := w.lastCapture bw + streamDelay f d w r) hbw₁ (by linarith) (by linarith)
    rw [← hB.clock, ← hB.clock] at hA1 hA2
    -- How far apart the query and the arrival are.
    obtain ⟨hq1, -⟩ := hU.host_sub hd (y := s₁) (y' := (w.speaker r).asked (β + 1))
      (hT.trans hTs) (by linarith) hβ
    obtain ⟨hq2, -⟩ := hU.host_sub hd (y := w.lastCapture bw + streamDelay f d w r)
      (y' := (w.speaker r).asked (β + 1)) (by linarith) hbw₂.le hβ
    rw [← hB.clock, ← hB.clock] at hq1 hq2
    have hTs' := hCmono hTs
    have hLq1 : (w.speaker r).asked (β + 1) - s₁ ≤ max t.exchangeWindow t.window / B.hostLo := by
      rw [le_div_iff₀ hBv.host_pos]
      have := le_max_left t.exchangeWindow t.window
      linarith
    have hLq2 : (w.speaker r).asked (β + 1) - (w.lastCapture bw + streamDelay f d w r)
        ≤ max t.exchangeWindow t.window / B.hostLo := by
      rw [le_div_iff₀ hBv.host_pos]
      have := le_max_right t.exchangeWindow t.window
      linarith
    -- The drift between the arrival and the query.
    have hA3 : ((w.clock w.sender).read s₁
          - (w.clock w.sender).read (w.lastCapture bw + streamDelay f d w r))
        - sl * ((w.clock (w.host r)).read s₁
          - (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r))
        ≤ (B.driftUp + B.driftDown) * (max t.exchangeWindow t.window / B.hostLo) := by
      rcases le_total (w.lastCapture bw + streamDelay f d w r) s₁ with hcase | hcase
      · obtain ⟨-, h1⟩ := drift_mem_of_undisturbed hB hd hU hBv hsl (by linarith) hcase
          (by linarith)
        unfold World.drift at h1
        have h2 : B.driftUp * (s₁ - (w.lastCapture bw + streamDelay f d w r))
            ≤ B.driftUp * (max t.exchangeWindow t.window / B.hostLo) :=
          mul_le_mul_of_nonneg_left (by linarith) hup
        have h3 : 0 ≤ B.driftDown * (max t.exchangeWindow t.window / B.hostLo) :=
          mul_nonneg hdown (by linarith)
        rw [add_mul]
        linarith
      · obtain ⟨h1, -⟩ := drift_mem_of_undisturbed hB hd hU hBv hsl (hT.trans hTs) hcase
          (by linarith)
        unfold World.drift at h1
        have h2 : B.driftDown * (w.lastCapture bw + streamDelay f d w r - s₁)
            ≤ B.driftDown * (max t.exchangeWindow t.window / B.hostLo) :=
          mul_le_mul_of_nonneg_left (by linarith) hdown
        have h3 : 0 ≤ B.driftUp * (max t.exchangeWindow t.window / B.hostLo) :=
          mul_nonneg hup (by linarith)
        rw [add_mul]
        linarith
    have hfit' := hfit.interval
    have e : sl * ((w.clock (w.host r)).read s₁
          - (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r))
        = sl * (w.clock (w.host r)).read s₁
          - sl * (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r) := by ring
    rw [e] at hA3
    have e' : sl * (0 - (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r))
        = -(sl * (w.clock (w.host r)).read (w.lastCapture bw + streamDelay f d w r)) := by ring
    rw [e'] at hv₀le
    have e'' : B.senderHi * f.roundTrip (w.host r) w.sender
        = B.senderHi * queryDelay f d w r + B.senderHi * streamDelay f d w r := by
      rw [← hRT]
      ring
    rw [e''] at hfit'
    have e₃ : s₁ + queryDelay f d w r - s₁ = queryDelay f d w r := by ring
    have e₄ : w.lastCapture bw + streamDelay f d w r - w.lastCapture bw
        = streamDelay f d w r := by ring
    rw [e₃] at hA1
    rw [e₄] at hA2
    linarith
  · -- The estimate against the truth, from the arrival that it rests on.
    obtain ⟨a, ha, hsa⟩ := exists_envelopeReading_eq hr (timingParts t) hs
    obtain ⟨b', hb'1, hb'2, hb'3, rfl⟩ := hwall a ha
    have hsa' : v + hf = (w.clock w.sender).read (w.lastCapture b')
        + sl * (outputAt t w r (β + 1) k
          - (w.clock (w.host r)).read (w.lastCapture b' + streamDelay f d w r)) + hf := by
      have h := hsa
      dsimp only [timingParts] at h
      rw [hout_eq, ← hsl_def, ← hf_def] at h
      exact h
    -- The drift from the arrival to the output sample.
    obtain ⟨hD1, hD2⟩ := drift_mem_of_undisturbed hB hd hU hBv hsl
      (x := w.lastCapture b' + streamDelay f d w r) (y := (w.speaker r).out k) (by linarith)
      (by linarith) hout
    obtain ⟨hq2, -⟩ := hU.host_sub hd (y := w.lastCapture b' + streamDelay f d w r)
      (y' := (w.speaker r).asked (β + 1)) (by linarith) hb'2.le hβ
    rw [← hB.clock, ← hB.clock] at hq2
    have hL1 : (w.speaker r).asked (β + 1) - (w.lastCapture b' + streamDelay f d w r)
        ≤ t.window / B.hostLo := by
      rw [le_div_iff₀ hBv.host_pos]
      linarith
    have hL : (w.speaker r).out k - (w.lastCapture b' + streamDelay f d w r)
        ≤ t.window / B.hostLo + outputLead m w r (β + 1) k / B.outputLo := by linarith
    have hD1' := mul_le_mul_of_nonneg_left hL hdown
    have hD2' := mul_le_mul_of_nonneg_left hL hup
    -- The stream's delay on the sender's clock.
    obtain ⟨hA1, hA2⟩ := hU.sender_sub hd (y := w.lastCapture b')
      (y' := w.lastCapture b' + streamDelay f d w r) hb'1.le (by linarith) (by linarith)
    rw [← hB.clock, ← hB.clock] at hA1 hA2
    have e₄ : w.lastCapture b' + streamDelay f d w r - w.lastCapture b'
        = streamDelay f d w r := by ring
    rw [e₄] at hA1 hA2
    -- The error of the expected reading at the output sample.
    have habs := abs_out_sub_outputAt_le hB hd t hrate hleadEq hU hBv hfit.ratio_lo
      hfit.ratio_hi hprev hβ hlead hout
    rw [show B.hostHi / B.outputLo - B.hostLo / B.outputHi = B.ratioWidth from rfl] at habs
    obtain ⟨hE1, hE2⟩ := abs_le.mp habs
    have hEnn : 0 ≤ B.ratioWidth * outputLead m w r (β + 1) k :=
      mul_nonneg (RateBands.ratioWidth_nonneg hBv) hlead
    have hT1 : sl * ((w.clock (w.host r)).read ((w.speaker r).out k) - outputAt t w r (β + 1) k)
        ≤ B.senderHi / B.hostLo * (B.ratioWidth * outputLead m w r (β + 1) k) :=
      (mul_le_mul_of_nonneg_left hE2 hsl0).trans (mul_le_mul_of_nonneg_right hsl.2 hEnn)
    have hT2 : -(B.senderHi / B.hostLo * (B.ratioWidth * outputLead m w r (β + 1) k))
        ≤ sl * ((w.clock (w.host r)).read ((w.speaker r).out k)
          - outputAt t w r (β + 1) k) := by
      have h1 := mul_le_mul_of_nonneg_left hE1 hsl0
      have h2 := mul_le_mul_of_nonneg_right hsl.2 hEnn
      rw [mul_neg] at h1
      linarith
    -- The error of the estimate, in parts.
    have key : (w.clock w.sender).read ((w.speaker r).out k) - (v + hf)
        = w.drift (w.host r) sl (w.lastCapture b' + streamDelay f d w r) ((w.speaker r).out k)
          + ((w.clock w.sender).read (w.lastCapture b' + streamDelay f d w r)
            - (w.clock w.sender).read (w.lastCapture b'))
          + sl * ((w.clock (w.host r)).read ((w.speaker r).out k) - outputAt t w r (β + 1) k)
          - hf := by
      unfold World.drift
      rw [hsa']
      ring
    rw [key]
    unfold estimateLow estimateHigh
    constructor <;> linarith

end Unisono.Solutions.Controller
