/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Views
public import Unisono.Solutions.FixedDelay.NoLoss
public import Unisono.Solutions.FixedDelay.Progress
public import Unisono.Spec.Limiter
public import Unisono.Spec.Models.GenerativeRates

/-!
# The controller at a held level when links and hosts pause

Consider a world in which the clocks of the hosts and of the audio devices
run at constant rates, each its own, the devices report exact timestamps,
and links and hosts pause (`GenerativeWorld.ConstantRates`). The delay
of a message is the least delay of its direction plus the backlogs it waits
for, and it has no upper bound. The controller
(`Unisono.Solutions.Controller`) holds the level at `L`.

**What is due.** When the estimate of the sender's clock at the host of
speaker `r` is the line of its undelayed clock exchanges (`exchangeLine`),
the position that is due at output sample `k` is the position captured

`L / (rate of the sender's clock) + asymmetry of the speaker's host`

before the sample leaves (`latencyOf`, `duePosition`,
`captured_duePosition`). Pauses do not move it.

**What plays** (`speaker_plays`). From some output sample on, each output
sample plays the position that is due if the message of the capture block
that holds the last frame the resampler needs (`neededBlock`) arrived
strictly before the playback device requested the sample's block, and plays
nothing of the source otherwise. A late block is a missed sample; it does
not shift what is due afterwards.

**The margin** (`margin`, `plays_eq_of_margin`). So an output sample plays
if and only if the message of the block it needs takes less than the
sample's margin: the time from the handover of that block to the request of
the sample's own block. The margin is more than `marginLeast` and at most
`marginMost`, two numbers that do not depend on the sample (`margin_mem`).
Both are the latency minus the request lead minus a span: for `marginMost`
the span of `lookahead - 1` frames, and for `marginLeast` the spans of a
playback block except one output sample and of a capture block and
`lookahead` frames except one frame. Hence a block that takes at most
`marginLeast` is in time, and one that takes at least `marginMost` is late
(`plays_of_delay`). Raising the level by one second of the sender's clock
raises both numbers by one second divided by the rate of that clock.

The estimate of the sender's clock is a hypothesis here (`ClockLineFrom`).
It is met without pauses by every estimator that is exact on undisturbed
exchanges (`Unisono.Solutions.Controller.Exact`), and with pauses by an
estimator that uses the exchanges of least round trip, once two exchanges
were not delayed (`Unisono.Solutions.Controller.Pauses`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

/-! ## What is due -/

/-- The line on which the undelayed clock exchanges of host `h` with the
sender lie: the reading of the sender's clock as a function of the reading
of the clock of `h`, moved by the asymmetry of the pair. Its slope is the
rate of the sender's clock divided by the rate of the clock of `h`. No host
can observe the asymmetry, so this line is the best that `h` can know of the
sender's clock. -/
def exchangeLine (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (h : H) : Line :=
  ⟨d.offset m.sender - Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * d.offset h
      + Real.exp (d.logRate m.sender)
        * (d.split h m.sender * f.roundTrip h m.sender
          - d.split m.sender h * f.roundTrip m.sender h) / 2,
    Real.exp (d.logRate m.sender) / Real.exp (d.logRate h)⟩

/-- The latency of speaker `r` at the level `L`, in true time: the level
divided by the rate of the sender's clock, plus the asymmetry of the
speaker's host, which is half the difference between the least delay from
the sender to it and the least delay back. -/
def latencyOf (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (L : ℝ) (r : Fin R) :
    ℝ :=
  L / Real.exp (d.logRate m.sender)
    + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
      - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2

/-- The position that is due at output sample `k` of speaker `r` at the
level `L`: the position captured `latencyOf` before the sample leaves. -/
def duePosition (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (L : ℝ) (r : Fin R) (k : ℕ) : ℝ :=
  m.rate * Real.exp (d.deviceLogRate none)
    * ((w.speaker r).out k - latencyOf m f d L r - w.source.capture 0)

/-- The capture block that holds the last frame that the resampler needs
for the position `x`: the frames less than `lookahead` frames away from `x`
end at frame `⌈x + lookahead⌉₊ - 1`. -/
def neededBlock (m : GenerativeWorld H R) (lookahead : ℕ+) (x : ℝ) : ℕ :=
  (⌈x + (lookahead : ℕ)⌉₊ - 1) / m.blockSize

/-- From true time `T₀` on, the estimate of the sender's clock at host `h`
is the line `ℓ`: at every step of the run whose event occurs after `T₀`. -/
def ClockLineFrom (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)
    (clockEst : ClockEstimator) (h : H) (ℓ : Line) (T₀ : Time) : Prop :=
  ∀ n, T₀ < σ.eventTime w lookahead n →
    clockEst (exchangesOf ((σ.states w lookahead n).views h)) = some ℓ

omit [DecidableEq H] in
/-- **The position that is due was captured the latency before the output
sample leaves.** -/
theorem captured_duePosition (hS : ConstantRates m f d w) (L : ℝ) (r : Fin R) (k : ℕ) :
    w.captured (duePosition m f d w L r k) = (w.speaker r).out k - latencyOf m f d L r := by
  have hρ := m.rate_pos.ne'
  have hg := (Real.exp_pos (d.deviceLogRate none)).ne'
  have hr := (Real.exp_pos (d.logRate m.sender)).ne'
  rw [hS.captured, duePosition, hS.capture 0]
  simp only [Nat.cast_zero, zero_div, add_zero]
  field_simp
  ring

omit [DecidableEq H] in
/-- From one output sample to the next, the position that is due advances by
the rate of the capture device's clock divided by the rate of the playback
device's clock. -/
theorem duePosition_succ (hS : ConstantRates m f d w) (L : ℝ) (r : Fin R) (k : ℕ) :
    duePosition m f d w L r (k + 1) - duePosition m f d w L r k
      = Real.exp (d.deviceLogRate none) / Real.exp (d.deviceLogRate (some (m.device r))) := by
  have hρ := m.rate_pos.ne'
  have hg := (Real.exp_pos (d.deviceLogRate (some (m.device r)))).ne'
  simp only [duePosition]
  rw [hS.out, hS.out]
  push_cast
  field_simp
  ring

/-! ## The clock exchanges in a host's view -/

omit [DecidableEq H] in
/-- Both samples of an undelayed exchange lie on lines of the same slope:
the ratio of the rate of the sender's clock to the rate of the host's. -/
theorem exchange_lines {θs θh rs rh δhs δsh s₁ : ℝ} (hrh : rh ≠ 0) :
    θs + rs * (s₁ + δhs) = (θs - rs / rh * θh + rs * δhs) + rs / rh * (θh + rh * s₁)
      ∧ θs + rs * (s₁ + δhs)
        = (θs - rs / rh * θh - rs * δsh) + rs / rh * (θh + rh * (s₁ + δhs + δsh)) := by
  constructor <;>
  · field_simp
    ring

/-- **Every clock exchange in a host's view is a true exchange.** In a world
built from a draw, the query left the host at some true time `s₁`, the
sender's reading is the reading of the sender's clock when the query
arrived, and the answer arrived when the draw says. -/
theorem exchange_of_built (hB : m.Builds f d w) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) {n : ℕ} {h : H} {x : Exchange}
    (hx : x ∈ plainExchangesOf
      (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead n).views
        h)) :
    ∃ s₁ : Time, x.sent = (w.clock h).read s₁
      ∧ x.received = (w.clock w.sender).read (d.arrival f h w.sender s₁)
      ∧ x.arrived
        = (w.clock h).read (d.arrival f w.sender h (d.arrival f h w.sender s₁)) := by
  obtain ⟨e, he, i, F, hobs, hread⟩ := mem_plainExchangesOf hx
  obtain ⟨j, hj, t, obs, hhj, rfl⟩ :=
    Solution.handled_of_mem_views w (FixedDelay.solution p) lookahead he
  simp only at hobs hread
  subst hobs
  obtain ⟨msg, hm, hdest, harr, -, hcont, -⟩ :=
    Solution.handled_received w (FixedDelay.solution p) lookahead hhj
  have hO := FixedDelay.origin_inFlight p w lookahead hsender j msg hm
  unfold FixedDelay.Origin at hO
  simp only [hcont] at hO
  obtain ⟨s₁, s₂, q, q', -, hs₁, hs₂, hdl₁, hdl₂⟩ := hO
  rw [hdest] at hs₁ hdl₁ hdl₂
  rw [harr, hB.deliver] at hdl₂
  rw [hB.deliver] at hdl₁
  have e2 : s₂ = d.arrival f h w.sender s₁ := (Option.some.inj hdl₁).symm
  have e4 : t = d.arrival f w.sender h s₂ := (Option.some.inj hdl₂).symm
  refine ⟨s₁, hs₁, ?_, ?_⟩
  · rw [hs₂, e2]
  · rw [← hread, e4, e2]

/-! ## The lines through the devices' timestamps -/

/-- The step that handles the handover of block `b` is the step at which
block `b` is the capture device's next block. -/
theorem handedNext_of_handled (σ : Solution H R Payload) (lookahead : ℕ+) {i b : ℕ}
    {frames : List (ℕ × ℝ)} {stamp : ℝ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b, .handed frames stamp)) :
    (σ.states w lookahead i).handedNext = b := by
  unfold Solution.handled at hi
  split at hi
  · rename_i b' hb'
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hi
    have hbb : b' = b := w.source.handed_strictMono.injective hi.1
    subst hbb
    have hmem := (earliest_spec _ _ _ hb').1
    rcases (σ.states w lookahead i).mem_due hmem with h | ⟨r'', h⟩ | ⟨q, _, h⟩ | ⟨q, _, h⟩
    · simp only [Due.handed.injEq] at h
      exact h.symm
    · simp at h
    · simp at h
    · simp at h
  · simp at hi
  · obtain ⟨msg, -, heq⟩ := Option.map_eq_some_iff.mp hi
    simp at heq
  · obtain ⟨u, -, heq⟩ := Option.map_eq_some_iff.mp hi
    simp at heq
  · simp at hi

/-- **The line through the capture device's timestamps is exact from the
second block on.** When the capture device hands over a block after its
first, an estimator that is exact on undisturbed reports returns the line
on which the timestamps lie: the member's start at frame zero, and a slope
of the rate of the sender's clock divided by the nominal rate and by the
rate of the capture device's clock. -/
theorem captureLine_exact (hS : ConstantRates m f d w) {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (σ : Solution H R Payload) (lookahead : ℕ+) {i b : ℕ}
    (hb : 1 ≤ b)
    (hhi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    deviceEst (captureReports ((σ.states w lookahead i).views w.sender
        ++ [⟨(w.clock w.sender).read (w.source.handed b),
          .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)⟩]))
      = some ⟨f.captureStart,
        Real.exp (d.logRate m.sender) / (m.rate * Real.exp (d.deviceLogRate none))⟩ := by
  have hcr : captureReports ((σ.states w lookahead i).views w.sender
        ++ [⟨(w.clock w.sender).read (w.source.handed b),
          .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)⟩])
      = captureReports ((σ.states w lookahead i).views w.sender)
        ++ [(w.source.first b, w.source.reported b)] := by
    simp [captureReports, List.filterMap_append, List.head?_map, CaptureDevice.head?_block]
  rw [hcr]
  refine hdev _ _ _ (fun e he => ?_) ?_
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨b', rfl⟩ := mem_captureReports w σ lookahead he
      exact hS.capture_reported b'
    · obtain rfl := List.mem_singleton.mp he
      exact hS.capture_reported b
  · have hnext := handedNext_of_handled σ lookahead hhi
    obtain ⟨n₀, hn₀, -, hearly₀⟩ := Solution.exists_handed_step w σ lookahead (m := i) (b := 0)
      (by omega)
    have hh₀ : σ.handled w lookahead n₀ = some (w.sender, w.source.handed 0,
        .handed ((w.source.block 0).map fun k => (k, w.target k)) (w.source.reported 0)) := by
      unfold Solution.handled
      rw [hearly₀]
    have hmem := Solution.mem_views_of_handled w σ lookahead hh₀ hn₀
    refine ⟨(w.source.first 0, w.source.reported 0), List.mem_append_left _ ?_,
      (w.source.first b, w.source.reported b),
      List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_⟩
    · exact List.mem_filterMap.mpr ⟨_, hmem, by
        simp [List.head?_map, CaptureDevice.head?_block]⟩
    · exact (w.source.first_strictMono (by omega : 0 < b)).ne

/-- **The line through a playback device's timestamps is exact from the
second request on.** When a speaker's device makes a request after its
first, an estimator that is exact on undisturbed reports returns the line
on which the timestamps lie: the member's start at output sample zero, and a
slope of the rate of the host's clock divided by the nominal rate and by the
rate of the device's clock. -/
theorem playbackLine_exact (hS : ConstantRates m f d w) {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (σ : Solution H R Payload) (lookahead : ℕ+) {n b : ℕ} {r : Fin R}
    (hb : 1 ≤ b) (hbn : (σ.states w lookahead n).askedNext r = b) :
    deviceEst (playbackReports r ((σ.states w lookahead n).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
          .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩]))
      = some ⟨f.speakerStart (m.device r), Real.exp (d.logRate (m.host r))
          / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))⟩ := by
  have hpr : playbackReports r ((σ.states w lookahead n).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
          .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩])
      = playbackReports r ((σ.states w lookahead n).views (w.host r))
        ++ [((w.speaker r).first b, (w.speaker r).reported b)] := by
    simp [playbackReports, List.filterMap_append, PlaybackDevice.head?_block]
  rw [hpr]
  refine hdev _ _ _ (fun e he => ?_) ?_
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨b', rfl⟩ := mem_playbackReports w σ lookahead he
      exact hS.speaker_reported r b'
    · obtain rfl := List.mem_singleton.mp he
      exact hS.speaker_reported r b
  · obtain ⟨n₀, hn₀, -, hearly₀⟩ := Solution.exists_asked_step w σ lookahead (m := n) (r := r)
      (b := 0) (by omega)
    have hh₀ := Solution.handled_of_asked w σ lookahead hearly₀
    have hmem := Solution.mem_views_of_handled w σ lookahead hh₀ hn₀
    refine ⟨((w.speaker r).first 0, (w.speaker r).reported 0), List.mem_append_left _ ?_,
      ((w.speaker r).first b, (w.speaker r).reported b),
      List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_⟩
    · exact List.mem_filterMap.mpr ⟨_, hmem, by simp [PlaybackDevice.head?_block]⟩
    · exact ((w.speaker r).first_strictMono (by omega : 0 < b)).ne

/-! ## What plays -/

/-- **What a speaker of the controller chooses and plays at a held level.**
Consider a world whose clocks run at constant rates, with exact timestamps
and with pauses of links and of hosts, a speaker `r` whose host is not the
sender's, a device estimator that is exact on undisturbed reports, and the
level held at `L`. Suppose that from some true time on the host's estimate
of the sender's clock is the line of its undelayed exchanges. Then, from
some output sample on, two things hold for output sample `k`. At the request
of the playback block that holds `k`, the position that the host chooses for
`k`, before the resampler checks the frames, is the position that is due, or
nothing. And `k` plays the position that is due if the message of the
capture block that the sample needs arrived strictly before the playback
device requested the sample's block, and plays nothing of the source
otherwise. -/
theorem speaker_chooses_plays (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      (∀ n b, k ∈ (w.speaker r).block b →
        ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead n).askedNext r = b →
        earliest (((solution p clockEst deviceEst (constantLevel L) :
              Solution H R Payload).states w lookahead n).key w)
            ((solution p clockEst deviceEst (constantLevel L) :
              Solution H R Payload).states w lookahead n).due = some (.asked r b) →
        ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).chosenAt w
            lookahead n r b k = none
          ∨ (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).chosenAt w
            lookahead n r b k = some (duePosition m f d w L r k)))
      ∧ (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k
        = if d.arrival f m.sender (m.host r)
              (w.source.handed (neededBlock m lookahead (duePosition m f d w L r k)))
            < (w.speaker r).asked (k / m.blockSize)
          then some (duePosition m f d w L r k) else none := by
  have hmore := sendsMore (R := R) p clockEst deviceEst (constantLevel L)
  have hsend : w.sender = m.sender := hS.builds.sender_eq
  have hhost : w.host r = m.host r := congrFun hS.builds.host_eq r
  have hsender : p.sender = w.sender := hps.trans hsend.symm
  have hhs : w.host r ≠ w.sender := by
    rw [hhost, hsend]
    exact hnos
  have hh : w.host r ∈ p.speakers := by
    rw [hhost]
    exact hpsp
  have hns : w.host r ≠ p.sender := by
    rw [hhost, hps]
    exact hnos
  have hA : ∀ i j s q, w.network.deliver i j s q = some (d.arrival f i j s) :=
    hS.builds.deliver
  have hρ := m.rate_pos
  have hrs := Real.exp_pos (d.logRate m.sender)
  have hrh := Real.exp_pos (d.logRate (m.host r))
  have hgc := Real.exp_pos (d.deviceLogRate none)
  have hgr := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have hB := m.blockSize_pos
  -- Late requests.
  obtain ⟨bmin, hbmin⟩ := hS.asked_unbounded r T₀
  obtain ⟨bK, hbK⟩ := hS.asked_unbounded r
    (latencyOf m f d L r + w.source.capture 0
      + (m.blockSize : ℝ) / (m.rate * Real.exp (d.deviceLogRate none)))
  choose step hstepb hstepe using FixedDelay.request_step_of_unbounded p w lookahead
    hS.handed_unbounded hS.asked_unbounded r
  have hfirst : ∀ b, (w.speaker r).first b = b * m.blockSize := hS.builds.speaker_first r
  have hmemblk : ∀ k, k ∈ (w.speaker r).block (k / m.blockSize) := by
    intro k
    unfold PlaybackDevice.block
    rw [List.mem_range'_1, hfirst, hfirst]
    have h1 := Nat.div_mul_le_self k m.blockSize
    have h2 := Nat.lt_div_mul_add hB (a := k)
    have h3 : (k / m.blockSize + 1) * m.blockSize
        = k / m.blockSize * m.blockSize + m.blockSize := by ring
    omega
  have hcapblk : ∀ n, n ∈ w.source.block (n / m.blockSize) := by
    intro n
    unfold CaptureDevice.block
    rw [List.mem_range'_1, hS.builds.capture_first, hS.builds.capture_first]
    have h1 := Nat.div_mul_le_self n m.blockSize
    have h2 := Nat.lt_div_mul_add hB (a := n)
    have h3 : (n / m.blockSize + 1) * m.blockSize
        = n / m.blockSize * m.blockSize + m.blockSize := by ring
    omega
  have hcard : ∀ b, (w.source.block b).toFinset.card = m.blockSize := by
    intro b
    unfold CaptureDevice.block
    rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range',
      hS.builds.capture_first, hS.builds.capture_first]
    have h3 : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
    omega
  have htime : ∀ b, (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w
      lookahead (step b) = (w.speaker r).asked b := fun b =>
    Solution.handled_time w (FixedDelay.solution p) lookahead
      (Solution.handled_of_asked w (FixedDelay.solution p) lookahead (hstepe b))
  -- The reading of the sender's clock, by the host's lines, when output sample `k` leaves.
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℝ, ∀ k, S k
      = (exchangeLine m f d (m.host r)).eval
        ((⟨f.speakerStart (m.device r), Real.exp (d.logRate (m.host r))
          / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))⟩ : Line).eval k) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨slope, hslope⟩ : ∃ slope : ℝ, slope = Real.exp (d.logRate m.sender)
      / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := ⟨_, rfl⟩
  have hslope0 : 0 < slope := by
    rw [hslope]
    exact div_pos hrs (mul_pos hρ hgr)
  have hSk : ∀ k : ℕ, S k = S 0 + slope * k := by
    intro k
    rw [hSdef, hSdef, hslope]
    simp only [Line.eval, exchangeLine]
    push_cast
    field_simp
    ring
  -- An exact header gives the position that is due.
  have hdueX : ∀ (hd : Header) (fb : ℕ) (k : ℕ), hd.first = fb →
      hd.capture = f.captureStart + Real.exp (d.logRate m.sender)
        / (m.rate * Real.exp (d.deviceLogRate none)) * (fb : ℝ) →
      hd.period = Real.exp (d.logRate m.sender) / (m.rate * Real.exp (d.deviceLogRate none)) →
      hd.level = L → hd.slope = 0 → hd.due (S k) = duePosition m f d w L r k := by
    intro hd fb k h1 h2 h3 h4 h5
    unfold Header.due
    rw [h1, h2, h3, h4, h5, hSdef]
    simp only [Line.eval, exchangeLine, duePosition, latencyOf]
    rw [hS.out, hS.capture 0]
    simp only [Nat.cast_zero, zero_div, add_zero]
    field_simp
    ring
  -- The header of block zero does not come from the capture line. From some reading
  -- of the sender's clock on, it covers no position.
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, ∀ i₃,
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).handled w
          lookahead i₃
        = some (w.sender, w.source.handed 0,
          .handed ((w.source.block 0).map fun k => (k, w.target k)) (w.source.reported 0)) →
      ∀ s, s₀ ≤ s →
        ¬ (blockHeader p deviceEst (constantLevel L)
            (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
                lookahead i₃).views w.sender
              ++ [⟨(w.clock w.sender).read (w.source.handed 0),
                .handed ((w.source.block 0).map fun k => (k, w.target k))
                  (w.source.reported 0)⟩])
            (w.source.first 0) (w.source.reported 0)).Covers m.blockSize s := by
    by_cases hex : ∃ i₃,
        (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).handled w
            lookahead i₃
          = some (w.sender, w.source.handed 0,
            .handed ((w.source.block 0).map fun k => (k, w.target k)) (w.source.reported 0))
    · obtain ⟨i₀, hi₀⟩ := hex
      obtain ⟨hd₀, hhd₀⟩ : ∃ hd₀ : Header, hd₀ = blockHeader p deviceEst (constantLevel L)
          (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
              lookahead i₀).views w.sender
            ++ [⟨(w.clock w.sender).read (w.source.handed 0),
              .handed ((w.source.block 0).map fun k => (k, w.target k))
                (w.source.reported 0)⟩])
          (w.source.first 0) (w.source.reported 0) := ⟨_, rfl⟩
      refine ⟨hd₀.capture + hd₀.level + (m.blockSize : ℝ) * (hd₀.period + hd₀.slope),
        fun i₃ hi₃ s hs hcov => ?_⟩
      have heq : i₃ = i₀ := Solution.handed_step_unique _ w lookahead
        (Solution.earliest_of_handled_handed _ w lookahead hi₃)
        (Solution.earliest_of_handled_handed _ w lookahead hi₀)
      subst heq
      rw [← hhd₀] at hcov
      obtain ⟨hp, -, hlt⟩ := hcov
      unfold Header.due at hlt
      have hlt' := (add_lt_add_iff_left _).mp hlt
      rw [div_lt_iff₀ hp] at hlt'
      linarith
    · exact ⟨0, fun i₃ hi₃ => absurd ⟨i₃, hi₃⟩ hex⟩
  obtain ⟨K₃, hK₃⟩ := exists_nat_ge ((s₀ - S 0) / slope)
  have hlateS : ∀ k, K₃ ≤ k → s₀ ≤ S k := by
    intro k hk
    have hk' : ((K₃ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : (s₀ - S 0) / slope ≤ k := hK₃.trans hk'
    rw [div_le_iff₀ hslope0] at h1
    rw [hSk]
    linarith
  -- Late positions are past the first block of the stream.
  have hXB : ∀ k, bK * m.blockSize ≤ k → (m.blockSize : ℝ) ≤ duePosition m f d w L r k := by
    intro k hk
    have hout : (w.speaker r).out ((w.speaker r).first bK) ≤ (w.speaker r).out k :=
      (w.speaker r).out_strictMono.monotone (by rw [hfirst]; exact hk)
    have hask := (w.speaker r).asked_before bK
    have hpos' : 0 < m.rate * Real.exp (d.deviceLogRate none) := mul_pos hρ hgc
    have h1 : (m.blockSize : ℝ) / (m.rate * Real.exp (d.deviceLogRate none))
        ≤ (w.speaker r).out k - latencyOf m f d L r - w.source.capture 0 := by linarith
    unfold duePosition
    calc (m.blockSize : ℝ)
        = m.rate * Real.exp (d.deviceLogRate none)
          * ((m.blockSize : ℝ) / (m.rate * Real.exp (d.deviceLogRate none))) := by
          field_simp
      _ ≤ m.rate * Real.exp (d.deviceLogRate none)
          * ((w.speaker r).out k - latencyOf m f d L r - w.source.capture 0) :=
          mul_le_mul_of_nonneg_left h1 hpos'.le
  refine ⟨max (max bmin 1 * m.blockSize) (max (bK * m.blockSize) K₃), fun k hk => ?_⟩
  have hk₀ : max bmin 1 * m.blockSize ≤ k := le_trans (le_max_left _ _) hk
  have hkK : bK * m.blockSize ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk₃ : K₃ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hb₀ : max bmin 1 ≤ k / m.blockSize := (Nat.le_div_iff_mul_le hB).mpr hk₀
  have hbmin' : bmin ≤ k / m.blockSize := le_trans (le_max_left _ _) hb₀
  have hb1 : 1 ≤ k / m.blockSize := le_trans (le_max_right _ _) hb₀
  have hT : T₀ < (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w
      lookahead (step (k / m.blockSize)) := by
    rw [htime]
    exact lt_of_lt_of_le hbmin ((w.speaker r).asked_strictMono.monotone hbmin')
  have hxB := hXB k hkK
  obtain ⟨x, hx⟩ : ∃ x, x = duePosition m f d w L r k := ⟨_, rfl⟩
  rw [← hx] at hxB ⊢
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hxB
  have haskedNext : ((solution p clockEst deviceEst (constantLevel L) :
      Solution H R Payload).states w lookahead (step (k / m.blockSize))).askedNext r
        = k / m.blockSize := by
    rw [Solution.askedNext_forget w Payload.plain lookahead hmore (step (k / m.blockSize))]
    exact hstepb (k / m.blockSize)
  have he' : earliest (((solution p clockEst deviceEst (constantLevel L) :
        Solution H R Payload).states w lookahead (step (k / m.blockSize))).key w)
      ((solution p clockEst deviceEst (constantLevel L) :
        Solution H R Payload).states w lookahead (step (k / m.blockSize))).due
      = some (.asked r (k / m.blockSize)) := by
    rw [(Solution.earliest_forget w Payload.plain lookahead hmore (step (k / m.blockSize))).2]
    exact hstepe (k / m.blockSize)
  -- The device line and the clock line.
  have hdl := playbackLine_exact hS hdev
    (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead hb1
    haskedNext
  have hcl : clockOf p clockEst (w.host r)
      (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (k / m.blockSize)),
          .asked r ((w.speaker r).block (k / m.blockSize))
            ((w.speaker r).reported (k / m.blockSize))⟩])
      = some (exchangeLine m f d (m.host r)) := by
    unfold clockOf
    rw [ite_eq_right hns]
    have hex : exchangesOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (k / m.blockSize))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (k / m.blockSize)),
            .asked r ((w.speaker r).block (k / m.blockSize))
              ((w.speaker r).reported (k / m.blockSize))⟩])
        = exchangesOf
          (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (k / m.blockSize))).views (w.host r)) := by
      simp [exchangesOf, List.filterMap_append]
    rw [hex, hhost]
    refine hline (step (k / m.blockSize)) ?_
    rw [Solution.eventTime_forget w Payload.plain lookahead hmore]
    exact hT
  have hsched : scheduleOf p deviceEst (constantLevel L) (w.host r)
      (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (k / m.blockSize)),
          .asked r ((w.speaker r).block (k / m.blockSize))
            ((w.speaker r).reported (k / m.blockSize))⟩])
      = headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r)) := by
    unfold scheduleOf
    rw [ite_eq_right hns, headersOf_append_asked]
  -- What the host plays is the position that the schedule gives when the sample leaves.
  have hposition : position p
      (scheduleOf p deviceEst (constantLevel L) (w.host r)
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (k / m.blockSize))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (k / m.blockSize)),
            .asked r ((w.speaker r).block (k / m.blockSize))
              ((w.speaker r).reported (k / m.blockSize))⟩]))
      (clockOf p clockEst (w.host r)
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (k / m.blockSize))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (k / m.blockSize)),
            .asked r ((w.speaker r).block (k / m.blockSize))
              ((w.speaker r).reported (k / m.blockSize))⟩]))
      (deviceEst (playbackReports r
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (k / m.blockSize))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (k / m.blockSize)),
            .asked r ((w.speaker r).block (k / m.blockSize))
              ((w.speaker r).reported (k / m.blockSize))⟩])))
      (((w.speaker r).block (k / m.blockSize)).headD 0)
      ((w.speaker r).reported (k / m.blockSize)) k
    = dueOf (headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r))) (S k) := by
    rw [hsched, hcl, hdl, hSdef]
    unfold position
    simp only [Option.map_some, Option.getD_some]
  -- Every header of the schedule is that of a block that arrived before the request.
  have hclass : ∀ y ∈ headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r)),
      ∃ b₂, d.arrival f w.sender (w.host r) (w.source.handed b₂)
          < (w.speaker r).asked (k / m.blockSize)
        ∧ y.2 = m.blockSize ∧ y.1.first = w.source.first b₂
        ∧ ((1 ≤ b₂
            ∧ y.1.capture = f.captureStart + Real.exp (d.logRate m.sender)
              / (m.rate * Real.exp (d.deviceLogRate none)) * (w.source.first b₂ : ℝ)
            ∧ y.1.period = Real.exp (d.logRate m.sender)
              / (m.rate * Real.exp (d.deviceLogRate none))
            ∧ y.1.level = L ∧ y.1.slope = 0)
          ∨ (b₂ = 0 ∧ ¬ y.1.Covers m.blockSize (S k))) := by
    intro y hy
    obtain ⟨e, he, i, stamp, F, hobs, hcount⟩ := mem_headersOf hy
    obtain ⟨i₂, hi₂, t₂, obs₂, hh₂, rfl⟩ := Solution.handled_of_mem_views w
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead he
    dsimp only at hobs
    subst hobs
    -- Where the message came from, in the controller's run.
    obtain ⟨msg, hmsg, -, -, -, hcont, -⟩ := Solution.handled_received w
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead hh₂
    obtain ⟨i₃, -, b₂, hh₃, hfr, hstamp, hheader⟩ :=
      block_header w p clockEst deviceEst (constantLevel L) lookahead i₂ hmsg hcont
    -- When it arrived and what it carried, in the baseline's run.
    have hf₂ := Solution.handled_forget w Payload.plain lookahead hmore i₂
    rw [hh₂] at hf₂
    simp only [Option.map_some, Observation.mapMsg, Payload.plain] at hf₂
    obtain ⟨msg', hmsg', hdest', harr', -, hcont', hframes'⟩ := Solution.handled_received w
      (FixedDelay.solution p : Solution H R FixedDelay.Payload) lookahead hf₂.symm
    have hO := FixedDelay.origin_inFlight p w lookahead hsender i₂ msg' hmsg'
    unfold FixedDelay.Origin at hO
    simp only [hcont'] at hO
    obtain ⟨b', -, hf', -, hfb', q, hq⟩ := hO
    have hbb : b' = b₂ := w.source.first_strictMono.injective (hf'.symm.trans hfr)
    subst hbb
    rw [hdest', hA] at hq
    have ht₂ : d.arrival f w.sender (w.host r) (w.source.handed b') = t₂ :=
      (Option.some.inj hq).trans harr'
    have hlt := Solution.received_lt_asked
      (FixedDelay.solution p : Solution H R FixedDelay.Payload) w lookahead hi₂.le hf₂.symm r
    rw [hstepb (k / m.blockSize)] at hlt
    refine ⟨b', by rw [ht₂]; exact hlt, ?_, hfr, ?_⟩
    · rw [hcount, ← hframes', hfb', hcard]
    · rcases Nat.eq_zero_or_pos b' with hb0 | hbpos
      · right
        refine ⟨hb0, ?_⟩
        subst hb0
        have hnot := hs₀ i₃ hh₃ (S k) (hlateS k hk₃)
        rw [← hheader] at hnot
        exact hnot
      · left
        have hlineC := captureLine_exact hS hdev
          (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead
          hbpos hh₃
        unfold blockHeader at hheader
        rw [hlineC] at hheader
        simp only [Option.map_some, Option.getD_some, Line.eval, constantLevel,
          Header.mk.injEq] at hheader
        obtain ⟨-, hcap, hper, hlev, hslo⟩ := hheader
        exact ⟨hbpos, hcap, hper, hlev, hslo⟩
  -- A covering header gives the position that is due.
  have hcover : ∀ y ∈ headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r)),
      y.1.Covers y.2 (S k) → y.1.due (S k) = x := by
    intro y hy hcov
    obtain ⟨b₂, -, hcnt, hfr, hexact | ⟨-, hnot⟩⟩ := hclass y hy
    · obtain ⟨-, hcap, hper, hlev, hslo⟩ := hexact
      rw [hx]
      exact hdueX y.1 (w.source.first b₂) k hfr hcap hper hlev hslo
    · rw [hcnt] at hcov
      exact absurd hcov hnot
  have hdue : dueOf (headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r))) (S k) = none
      ∨ dueOf (headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r))) (S k) = some x := by
    classical
    unfold dueOf
    cases hfind : List.find? (fun e : Header × ℕ => decide (e.1.Covers e.2 (S k)))
        (headersOf
          (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (k / m.blockSize))).views (w.host r))) with
    | none => exact Or.inl rfl
    | some y =>
      right
      have hmem := List.mem_of_find?_eq_some hfind
      have hcov : y.1.Covers y.2 (S k) := by simpa using List.find?_some hfind
      rw [Option.map_some, hcover y hmem hcov]
  -- The block of the position that is due.
  obtain ⟨bX, hbX⟩ : ∃ bX, bX = ⌊x⌋₊ / m.blockSize := ⟨_, rfl⟩
  have hBx : (m.blockSize : ℝ) ≤ x := hxB
  have hfloorB : m.blockSize ≤ ⌊x⌋₊ := Nat.le_floor hBx
  have hbX1 : 1 ≤ bX := by
    rw [hbX]
    exact (Nat.le_div_iff_mul_le hB).mpr (by simpa using hfloorB)
  have hdueSome : d.arrival f w.sender (w.host r) (w.source.handed bX)
        < (w.speaker r).asked (k / m.blockSize) →
      dueOf (headersOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead (step (k / m.blockSize))).views (w.host r))) (S k) = some x := by
    intro harrX
    classical
    -- The message of that block was handled before the request.
    obtain ⟨i₁, hi₁, hh₁⟩ := FixedDelay.block_handled_of_noLoss p w lookahead hA hsender hnodup
      hcopies hh hhs (b := bX) (k := step (k / m.blockSize)) (by rw [htime]; exact harrX)
    have hf₁ := Solution.handled_forget w Payload.plain lookahead hmore i₁
    rw [hh₁] at hf₁
    obtain ⟨⟨h', t', obs'⟩, hσh, heq⟩ := Option.map_eq_some_iff.mp hf₁
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hobs⟩ := heq
    obtain ⟨c₁, F₁, hobs₁, hpl₁⟩ : ∃ (c₁ : Payload) (F₁ : Finset ℕ),
        obs' = .received w.sender c₁ F₁
        ∧ c₁.plain = .block (w.source.first bX) (w.source.reported bX) := by
      cases obs' with
      | handed frames stamp => simp [Observation.mapMsg] at hobs
      | asked r' outputs stamp => simp [Observation.mapMsg] at hobs
      | timer => simp [Observation.mapMsg] at hobs
      | received j c' F' =>
        simp only [Observation.mapMsg, Observation.received.injEq] at hobs
        obtain ⟨rfl, hpl, -⟩ := hobs
        exact ⟨c', F', rfl, hpl⟩
    obtain ⟨cp₁, pd₁, lv₁, sl₁, hc₁⟩ : ∃ cp₁ pd₁ lv₁ sl₁ : ℝ,
        c₁ = .block (w.source.first bX) (w.source.reported bX) cp₁ pd₁ lv₁ sl₁ := by
      cases c₁ with
      | block f' st' cp pd lv sl =>
        simp only [Payload.plain, FixedDelay.Payload.block.injEq] at hpl₁
        obtain ⟨rfl, rfl⟩ := hpl₁
        exact ⟨cp, pd, lv, sl, rfl⟩
      | ask sent need => simp [Payload.plain] at hpl₁
      | answer sent received => simp [Payload.plain] at hpl₁
    subst hobs₁ hc₁
    have hmem₁ := Solution.mem_views_of_handled w
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead hσh hi₁
    have hentry := headersOf_mem hmem₁ rfl
    -- Its header is exact and covers the position that is due.
    obtain ⟨b₂, -, hcnt, hfr, hexact | ⟨hb0, -⟩⟩ := hclass _ hentry
    · obtain ⟨-, hcap, hper, hlev, hslo⟩ := hexact
      dsimp only at hcnt hfr hcap hper hlev hslo
      have hbb : b₂ = bX := (w.source.first_strictMono.injective hfr).symm
      subst hbb
      have hdueY : (⟨w.source.first b₂, cp₁, pd₁, lv₁, sl₁⟩ : Header).due (S k) = x := by
        rw [hx]
        exact hdueX _ (w.source.first b₂) k rfl hcap hper hlev hslo
      have hcov : (⟨w.source.first b₂, cp₁, pd₁, lv₁, sl₁⟩ : Header).Covers F₁.card (S k) := by
        refine ⟨?_, ?_, ?_⟩
        · show 0 < pd₁ + sl₁
          rw [hper, hslo, add_zero]
          exact div_pos hrs (mul_pos hρ hgc)
        · rw [hdueY, hS.builds.capture_first, hbX]
          have h1 := Nat.div_mul_le_self ⌊x⌋₊ m.blockSize
          have h2 : ((⌊x⌋₊ / m.blockSize * m.blockSize : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
            exact_mod_cast h1
          exact h2.trans (Nat.floor_le hx0)
        · rw [hdueY, hcnt, hS.builds.capture_first, hbX]
          have h1 := Nat.lt_div_mul_add hB (a := ⌊x⌋₊)
          have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ)
              ≤ ((⌊x⌋₊ / m.blockSize * m.blockSize + m.blockSize : ℕ) : ℝ) := by
            exact_mod_cast h1
          have h3 := Nat.lt_floor_add_one x
          push_cast at h2 ⊢
          linarith
      rcases hdue with hnone | hsome
      · exfalso
        unfold dueOf at hnone
        rw [Option.map_eq_none_iff] at hnone
        have hall := List.find?_eq_none.mp hnone _ hentry
        simp only [decide_eq_true_eq] at hall
        exact hall hcov
      · exact hsome
    · dsimp only at hfr
      have hbb : b₂ = bX := (w.source.first_strictMono.injective hfr).symm
      omega
  refine ⟨fun n b hkb hnb hne => ?_, ?_⟩
  · -- What the host chooses at the request of the block of `k`.
    have hbk : b = k / m.blockSize := by
      have h1 := hkb
      have e : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
      unfold PlaybackDevice.block at h1
      rw [List.mem_range'_1, hfirst, hfirst, e] at h1
      have h2 : k < b * m.blockSize + m.blockSize := by
        have h3 := h1.2
        generalize b * m.blockSize = q at h3 ⊢
        omega
      exact (Nat.div_eq_of_lt_le h1.1 (by rw [e]; exact h2)).symm
    subst hbk
    obtain rfl := Solution.asked_step_unique _ w lookahead hnb hne haskedNext he'
    unfold Solution.chosenAt World.askedEvent
    rw [plays_asked, hposition]
    exact hdue
  -- The frames that the resampler needs are held exactly when the last of them is.
  rw [Solution.plays_of_asked_step w _ lookahead haskedNext he' (hmemblk k), plays_asked,
    hposition, Solution.held_forget w Payload.plain lookahead hmore (step (k / m.blockSize)),
    ← hsend, ← hhost]
  have ha1 : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
  have hy : 0 < x + ((lookahead : ℕ) : ℝ) := by linarith
  have hceil : 0 < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr hy
  have hlt1 := Nat.ceil_lt_add_one hy.le
  have hle1 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
  obtain ⟨N, hN⟩ : ∃ N, N + 1 = ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := ⟨_, Nat.sub_add_cancel hceil⟩
  have hNc : ((N : ℝ) + 1) = (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℝ) := by exact_mod_cast hN
  have hNeed : neededBlock m lookahead x = N / m.blockSize := by
    unfold neededBlock
    rw [← hN, Nat.add_sub_cancel]
  rw [hNeed]
  have hiff : (0 ≤ x ∧ ∀ n : ℕ, |(n : ℝ) - x| < ((lookahead : ℕ) : ℝ) →
        n ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
          (step (k / m.blockSize))).held (w.host r))
      ↔ d.arrival f w.sender (w.host r) (w.source.handed (N / m.blockSize))
        < (w.speaker r).asked (k / m.blockSize) := by
    constructor
    · rintro ⟨-, hall⟩
      have hNheld := hall N (by
        rw [abs_lt]
        constructor <;> linarith)
      exact (FixedDelay.mem_held_iff_arrived p w lookahead hA hsender hnodup hcopies hh hhs
        (hstepb (k / m.blockSize)) (hstepe (k / m.blockSize)) (hcapblk N)).mp hNheld
    · intro harr
      refine ⟨hx0, fun n hn => ?_⟩
      have hnlt : (n : ℝ) < (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℝ) := by
        have := (abs_lt.mp hn).2
        linarith
      have hnN : n ≤ N := by
        have : n < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := by exact_mod_cast hnlt
        omega
      have hblk : n / m.blockSize ≤ N / m.blockSize := Nat.div_le_div_right hnN
      have hhand := w.source.handed_strictMono.monotone hblk
      have harr' := hS.arrival_mono w.sender (w.host r) hhand
      exact (FixedDelay.mem_held_iff_arrived p w lookahead hA hsender hnodup hcopies hh hhs
        (hstepb (k / m.blockSize)) (hstepe (k / m.blockSize)) (hcapblk n)).mpr
        (lt_of_le_of_lt harr' harr)
  by_cases harr : d.arrival f w.sender (w.host r) (w.source.handed (N / m.blockSize))
      < (w.speaker r).asked (k / m.blockSize)
  · -- The block of the position arrived no later than the block of the last frame needed.
    have hfloorN : ⌊x⌋₊ ≤ N := Nat.floor_le_of_le (by linarith)
    have hblk : bX ≤ N / m.blockSize := by
      rw [hbX]
      exact Nat.div_le_div_right hfloorN
    have harrX := lt_of_le_of_lt
      (hS.arrival_mono w.sender (w.host r) (w.source.handed_strictMono.monotone hblk)) harr
    rw [hdueSome harrX, ite_eq_left harr]
    simp only [playable]
    rw [ite_eq_left (hiff.mpr harr)]
  · rw [ite_eq_right harr]
    rcases hdue with hnone | hsome
    · rw [hnone]
      rfl
    · rw [hsome]
      simp only [playable]
      rw [ite_eq_right (fun h => harr (hiff.mp h))]

/-- **What a speaker of the controller plays at a held level.** Consider a
world whose clocks run at constant rates, with exact timestamps and with
pauses of links and of hosts, a speaker `r` whose host is not the sender's,
a device estimator that is exact on undisturbed reports, and the level held
at `L`. Suppose that from some true time on the host's estimate of the
sender's clock is the line of its undelayed exchanges. Then, from some
output sample on, output sample `k` plays the position that is due if the
message of the capture block that the sample needs arrived strictly before
the playback device requested the sample's block, and plays nothing of the
source otherwise. -/
theorem speaker_plays (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k
        = if d.arrival f m.sender (m.host r)
              (w.source.handed (neededBlock m lookahead (duePosition m f d w L r k)))
            < (w.speaker r).asked (k / m.blockSize)
          then some (duePosition m f d w L r k) else none := by
  obtain ⟨K, hK⟩ := speaker_chooses_plays p hS lookahead hdev L hps hnodup hcopies r hnos hpsp
    hline
  exact ⟨K, fun k hk => (hK k hk).2⟩

/-- **What a speaker of the controller chooses at a held level.** In the
setting of `speaker_plays`, from some output sample on: at the request of
the playback block that holds output sample `k`, the position that the host
chooses for `k`, before the resampler checks the frames, is the position
that is due, or nothing. -/
theorem speaker_chooses (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ n b k, K ≤ k → k ∈ (w.speaker r).block b →
        ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
          lookahead n).askedNext r = b →
        earliest (((solution p clockEst deviceEst (constantLevel L) :
              Solution H R Payload).states w lookahead n).key w)
            ((solution p clockEst deviceEst (constantLevel L) :
              Solution H R Payload).states w lookahead n).due = some (.asked r b) →
        ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).chosenAt w
            lookahead n r b k = none
          ∨ (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).chosenAt w
            lookahead n r b k = some (duePosition m f d w L r k)) := by
  obtain ⟨K, hK⟩ := speaker_chooses_plays p hS lookahead hdev L hps hnodup hcopies r hnos hpsp
    hline
  exact ⟨K, fun n b k hk hkb hnb hne => (hK k hk).1 n b hkb hnb hne⟩

/-! ## The margin -/

/-- How long the message of capture block `c` takes to reach the host of
speaker `r`: from the block's handover to its arrival. It is the least delay
of the direction plus the backlogs that the message waits for. -/
def blockDelay (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (r : Fin R) (c : ℕ) : ℝ :=
  d.arrival f m.sender (m.host r) (w.source.handed c) - w.source.handed c

/-- The margin of output sample `k` of speaker `r` at the level `L`: the
time from the handover of the capture block that the sample needs to the
request of the sample's own block. It is how long the message of that
capture block may take. -/
def margin (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (lookahead : ℕ+) (L : ℝ) (r : Fin R) (k : ℕ) : ℝ :=
  (w.speaker r).asked (k / m.blockSize)
    - w.source.handed (neededBlock m lookahead (duePosition m f d w L r k))

/-- The least margin of an output sample of speaker `r` at the level `L`:
the latency minus the request lead on the device's clock, the span of a
playback block except one output sample, and the span of a capture block and
of the resampler's lookahead except one frame. -/
def marginLeast (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (lookahead : ℕ+)
    (L : ℝ) (r : Fin R) : ℝ :=
  latencyOf m f d L r - m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
    - ((m.blockSize : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
    - (((lookahead : ℕ) : ℝ) + (m.blockSize : ℝ) - 1)
      / (m.rate * Real.exp (d.deviceLogRate none))

/-- The largest margin of an output sample of speaker `r` at the level `L`:
the latency minus the request lead on the device's clock and the span of the
resampler's lookahead except one frame. -/
def marginMost (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (lookahead : ℕ+)
    (L : ℝ) (r : Fin R) : ℝ :=
  latencyOf m f d L r - m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
    - (((lookahead : ℕ) : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate none))

omit [DecidableEq H] in
/-- **The margin of every output sample lies between two numbers that do not
depend on the sample**, once the position that is due is past the start of
the stream. -/
theorem margin_mem (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ) (r : Fin R)
    (k : ℕ) (hx0 : 0 ≤ duePosition m f d w L r k) :
    marginLeast m f d lookahead L r < margin m f d w lookahead L r k
      ∧ margin m f d w lookahead L r k ≤ marginMost m f d lookahead L r := by
  have hρ := m.rate_pos
  have hgc := Real.exp_pos (d.deviceLogRate none)
  have hgr := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have hrs := Real.exp_pos (d.logRate m.sender)
  have hB := m.blockSize_pos
  obtain ⟨x, hx⟩ : ∃ x, x = duePosition m f d w L r k := ⟨_, rfl⟩
  rw [← hx] at hx0
  have ha1 : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
  have hy : 0 < x + ((lookahead : ℕ) : ℝ) := by linarith
  have hceil : 0 < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr hy
  have hlt1 := Nat.ceil_lt_add_one hy.le
  have hle1 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
  obtain ⟨N, hN⟩ : ∃ N, N + 1 = ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := ⟨_, Nat.sub_add_cancel hceil⟩
  have hNc : ((N : ℝ) + 1) = (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℝ) := by exact_mod_cast hN
  have hNeed : neededBlock m lookahead x = N / m.blockSize := by
    unfold neededBlock
    rw [← hN, Nat.add_sub_cancel]
  -- The block of the output sample and the block of the frame, in real numbers.
  obtain ⟨β, hβ⟩ : ∃ β, β = k / m.blockSize := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = N / m.blockSize := ⟨_, rfl⟩
  have hβ1 : (β : ℝ) * m.blockSize ≤ k := by
    have := Nat.div_mul_le_self k m.blockSize
    rw [← hβ] at this
    exact_mod_cast this
  have hβ2 : (k : ℝ) ≤ (β : ℝ) * m.blockSize + m.blockSize - 1 := by
    have := Nat.lt_div_mul_add hB (a := k)
    rw [← hβ] at this
    have h' : k + 1 ≤ β * m.blockSize + m.blockSize := this
    have h'' : ((k + 1 : ℕ) : ℝ) ≤ ((β * m.blockSize + m.blockSize : ℕ) : ℝ) := by
      exact_mod_cast h'
    push_cast at h''
    linarith
  have hc1 : (c : ℝ) * m.blockSize ≤ N := by
    have := Nat.div_mul_le_self N m.blockSize
    rw [← hc] at this
    exact_mod_cast this
  have hc2 : (N : ℝ) ≤ (c : ℝ) * m.blockSize + m.blockSize - 1 := by
    have := Nat.lt_div_mul_add hB (a := N)
    rw [← hc] at this
    have h' : N + 1 ≤ c * m.blockSize + m.blockSize := this
    have h'' : ((N + 1 : ℕ) : ℝ) ≤ ((c * m.blockSize + m.blockSize : ℕ) : ℝ) := by
      exact_mod_cast h'
    push_cast at h''
    linarith
  -- The margin, by the output sample's place in its block and the frame's place in its block.
  obtain ⟨u, hu⟩ : ∃ u, u = 1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = 1 / (m.rate * Real.exp (d.deviceLogRate none)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]
    exact one_div_pos.mpr (mul_pos hρ hgr)
  have hv0 : 0 < v := by
    rw [hv]
    exact one_div_pos.mpr (mul_pos hρ hgc)
  have hmargin : margin m f d w lookahead L r k
      = latencyOf m f d L r - m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
        - ((k : ℝ) - (β : ℝ) * m.blockSize) * u
        - (((c : ℝ) + 1) * m.blockSize - 1 - x) * v := by
    have hask := hS.asked r β
    rw [hS.builds.speaker_first, hS.out] at hask
    have e : ((β * m.blockSize : ℕ) : ℝ) = (β : ℝ) * m.blockSize := by push_cast; ring
    rw [e] at hask
    have hxk : x = m.rate * Real.exp (d.deviceLogRate none)
        * ((f.speakerStart (m.device r) - d.offset (m.host r)) / Real.exp (d.logRate (m.host r))
            + (k : ℝ) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - latencyOf m f d L r
          - (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)) := by
      rw [hx, duePosition, hS.out, hS.capture 0]
      simp only [Nat.cast_zero, zero_div, add_zero]
    unfold margin
    rw [← hx, hNeed, ← hβ, ← hc, hS.handed, hu, hv, hxk]
    have hask' : (w.speaker r).asked β
        = (f.speakerStart (m.device r) - d.offset (m.host r)) / Real.exp (d.logRate (m.host r))
          + (β : ℝ) * m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - m.lead / Real.exp (d.deviceLogRate (some (m.device r))) := by linarith
    rw [hask']
    field_simp
    ring
  have h1 : 0 ≤ ((k : ℝ) - (β : ℝ) * m.blockSize) * u :=
    mul_nonneg (by linarith) hu0.le
  have h2 : ((k : ℝ) - (β : ℝ) * m.blockSize) * u ≤ ((m.blockSize : ℝ) - 1) * u :=
    mul_le_mul_of_nonneg_right (by linarith) hu0.le
  have h3 : (((lookahead : ℕ) : ℝ) - 1) * v ≤ (((c : ℝ) + 1) * m.blockSize - 1 - x) * v :=
    mul_le_mul_of_nonneg_right (by linarith) hv0.le
  have h4 : (((c : ℝ) + 1) * m.blockSize - 1 - x) * v
      < (((lookahead : ℕ) : ℝ) + (m.blockSize : ℝ) - 1) * v :=
    mul_lt_mul_of_pos_right (by linarith) hv0
  have eL : marginLeast m f d lookahead L r
      = latencyOf m f d L r - m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
        - ((m.blockSize : ℝ) - 1) * u
        - (((lookahead : ℕ) : ℝ) + (m.blockSize : ℝ) - 1) * v := by
    rw [marginLeast, hu, hv]
    ring
  have eM : marginMost m f d lookahead L r
      = latencyOf m f d L r - m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
        - (((lookahead : ℕ) : ℝ) - 1) * v := by
    rw [marginMost, hv]
    ring
  rw [hmargin, eL, eM]
  constructor <;> linarith

/-- **An output sample plays if and only if the block it needs takes less
than the sample's margin.** The statement of `speaker_plays` in terms of the
delay of the block's message. -/
theorem plays_eq_of_margin (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      0 ≤ duePosition m f d w L r k ∧
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k
        = if blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
            < margin m f d w lookahead L r k
          then some (duePosition m f d w L r k) else none := by
  obtain ⟨K, hK⟩ := speaker_plays p hS lookahead hdev L hps hnodup hcopies r hnos hpsp hline
  obtain ⟨bK, hbK⟩ := hS.asked_unbounded r (latencyOf m f d L r + w.source.capture 0)
  refine ⟨max K (bK * m.blockSize), fun k hk => ⟨?_, ?_⟩⟩
  · have hkK := le_trans (le_max_right _ _) hk
    have hout : (w.speaker r).out ((w.speaker r).first bK) ≤ (w.speaker r).out k :=
      (w.speaker r).out_strictMono.monotone (by rw [hS.builds.speaker_first]; exact hkK)
    have hask := (w.speaker r).asked_before bK
    unfold duePosition
    exact mul_nonneg (mul_pos m.rate_pos (Real.exp_pos _)).le (by linarith)
  · rw [hK k (le_trans (le_max_left _ _) hk)]
    have hiff : d.arrival f m.sender (m.host r)
          (w.source.handed (neededBlock m lookahead (duePosition m f d w L r k)))
          < (w.speaker r).asked (k / m.blockSize)
        ↔ blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
          < margin m f d w lookahead L r k := by
      unfold blockDelay margin
      constructor <;> intro h <;> linarith
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · rfl

/-- **A block that takes at most the least margin is in time, and one that
takes at least the largest margin is late.** From some output sample on: if
the message of the capture block that output sample `k` needs takes at most
`marginLeast`, the sample plays the position that is due; if it takes at
least `marginMost`, the sample plays nothing of the source. -/
theorem plays_of_delay (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      (blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
          ≤ marginLeast m f d lookahead L r →
        (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k = some (duePosition m f d w L r k))
      ∧ (marginMost m f d lookahead L r
          ≤ blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k)) →
        (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k = none) := by
  obtain ⟨K, hK⟩ := plays_eq_of_margin p hS lookahead hdev L hps hnodup hcopies r hnos hpsp hline
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨hx0, hplays⟩ := hK k hk
  obtain ⟨hlo, hhi⟩ := margin_mem hS lookahead L r k hx0
  constructor
  · intro hdel
    rw [hplays, ite_eq_left (lt_of_le_of_lt hdel hlo)]
  · intro hdel
    rw [hplays, ite_eq_right (not_lt.mpr (le_trans hhi hdel))]

end Unisono.Solutions.Controller
