/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Views
public import Unisono.Solutions.FixedDelay.Latency
public import Unisono.Spec.ExactLatency
public import Unisono.Spec.Models.GenerativeRates

/-!
# The controller with clocks at constant rates

Consider a world in which the clocks of the hosts and of the audio devices
run at constant rates, each its own, the links have constant delays, and the
devices report exact timestamps (`GenerativeWorld.ConstantRates`). The
baseline goes wrong in such a world in two ways: its clock estimate goes
stale between one clock query and the next, and it takes the rate of a
device for the rate of its host's clock. The controller
(`Unisono.Solutions.Controller`) measures both.

**Theorem** (`playsAtLatencies`). In such a world, with estimators that are
exact on undisturbed data and the level held at `L`, from some output sample
on every output sample of each speaker plays the sound captured exactly

`L / (rate of the sender's clock) + asymmetry of the speaker's host`

before the sample leaves. The asymmetry of a host is half the difference
between the delay from the sender to it and the delay back. The first term
is the level in true time: the level is counted on the sender's clock, and
no host can observe how fast that clock runs against true time.

The proof uses the baseline's run, which the controller shares once the
further fields of its messages are forgotten.

* Every clock exchange in a host's view is a true exchange
  (`exchange_of_view`), and after some time the view holds two exchanges
  whose queries were sent at different readings (`exists_two_exchanges`), so
  the clock line is exact.
* From its second block on, the capture device's timestamps lie on a line
  with two different points, so the header of every such block is exact
  (`captureLine_exact`); the same holds for the timestamps of a playback
  device from its second request on (`playbackLine_exact`).
* The schedule that a host follows at a late request is the header of a
  block from the second on.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

/-! ## Arithmetic -/

/-- Both samples of an undisturbed exchange lie on lines of the same slope:
the ratio of the rate of the sender's clock to the rate of the host's. -/
private theorem exchange_lines {θs θh rs rh δhs δsh s₁ : ℝ} (hrh : rh ≠ 0) :
    θs + rs * (s₁ + δhs) = (θs - rs / rh * θh + rs * δhs) + rs / rh * (θh + rh * s₁)
      ∧ θs + rs * (s₁ + δhs)
        = (θs - rs / rh * θh - rs * δsh) + rs / rh * (θh + rh * (s₁ + δhs + δsh)) := by
  constructor <;>
  · field_simp
    ring

/-- The frames around a position arrive before the request, under the
delivery margin. -/
private theorem margin_arith {a mB ρ lead ε δsh δhs L rs ok of ask : ℝ} (hε : ε < 1 / 2)
    (hrs : rs ≤ 1 + ε) (hrs0 : 0 < rs) (hL : 0 ≤ L)
    (hlat : ((a + 2 * (mB - 1)) / ρ + lead) / (1 - ε) + (δsh + δhs) / 2 < L / (1 + ε))
    (hout : ok - of ≤ (1 + ε / (1 - ε)) / ρ * (mB - 1))
    (hask : of - ask ≤ lead / (1 - ε)) :
    ok - (L / rs + (δsh - δhs) / 2) + (a + (mB - 1)) * (1 + ε / (1 - ε)) / ρ + 0 + δsh < ask := by
  have h1ε : (1 - ε) ≠ 0 := by linarith
  have h1 : L / (1 + ε) ≤ L / rs := by gcongr
  have e1 : 1 + ε / (1 - ε) = 1 / (1 - ε) := by
    field_simp
    ring
  have e2 : ((a + 2 * (mB - 1)) / ρ + lead) / (1 - ε)
      = 1 / (1 - ε) / ρ * (mB - 1) + (a + (mB - 1)) * (1 / (1 - ε)) / ρ + lead / (1 - ε) := by
    field_simp
    ring
  rw [e1] at hout ⊢
  rw [e2] at hlat
  linarith

/-! ## The clock exchanges in a host's view -/

/-- **Every clock exchange in a host's view is a true exchange.** The query
left the host at some true time; the sender's reading is the reading of the
sender's clock one delay later; and the answer arrived one more delay
later. -/
theorem exchange_of_view (hS : ConstantRates m f d w) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) {n : ℕ} {h : H} {x : Exchange}
    (hx : x ∈ plainExchangesOf
      (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead n).views
        h)) :
    ∃ s₁ : Time, x.sent = (w.clock h).read s₁
      ∧ x.received = (w.clock w.sender).read (s₁ + d.split h w.sender * f.roundTrip h w.sender)
      ∧ x.arrived = (w.clock h).read (s₁ + d.split h w.sender * f.roundTrip h w.sender
          + d.split w.sender h * f.roundTrip w.sender h) := by
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
  rw [harr, hS.deliver] at hdl₂
  rw [hS.deliver] at hdl₁
  have e2 : s₂ = s₁ + d.split h w.sender * f.roundTrip h w.sender := (Option.some.inj hdl₁).symm
  have e4 : t = s₂ + d.split w.sender h * f.roundTrip w.sender h := (Option.some.inj hdl₂).symm
  refine ⟨s₁, hs₁, ?_, ?_⟩
  · rw [hs₂, e2]
  · rw [← hread, e4, e2]

/-- **After some time, a host's view holds two clock exchanges whose queries
were sent at different readings.** -/
theorem exists_two_exchanges (hS : ConstantRates m f d w) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period)
    (r : Fin R) (hhs : w.host r ≠ w.sender) :
    ∃ T₀ : Time, ∀ n,
      T₀ < (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w lookahead n →
      ∃ x ∈ plainExchangesOf
          (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
            n).views (w.host r)),
        ∃ x' ∈ plainExchangesOf
          (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
            n).views (w.host r)),
          x.sent ≠ x'.sent := by
  have hw := hS.withinBounds hε0 hε hrates hdevices
  have hw' := hw
  obtain ⟨-, -, hspk, -, -, -, hlead, -, -, -, -⟩ := hw'
  have hρ := w.rate_pos
  have hδ₁ := hS.delay_pos (w.host r) w.sender
  have hδ₂ := hS.delay_pos w.sender (w.host r)
  have hP : 0 ≤ p.period / (1 - ε) := div_nonneg hperiod (by linarith)
  obtain ⟨b₁, hb₁⟩ := PlaybackDevice.asked_unbounded hρ (hspk r)
    (rateBounds m f d ε hε0 hε hS.delay_pos).deviceRate_lt_one (hlead r)
    ((w.speaker r).asked 0 + d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender
      + d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r))
  obtain ⟨b₂, hb₂⟩ := PlaybackDevice.asked_unbounded hρ (hspk r)
    (rateBounds m f d ε hε0 hε hS.delay_pos).deviceRate_lt_one (hlead r)
    ((w.speaker r).asked b₁ + p.period / (1 - ε))
  refine ⟨(w.speaker r).asked b₂
    + d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender
    + d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r), fun n hn => ?_⟩
  obtain ⟨k₀, -, hk₀e⟩ := FixedDelay.request_step p w _ hw lookahead r 0
  obtain ⟨k₁, -, hk₁e⟩ := FixedDelay.request_step p w _ hw lookahead r b₁
  obtain ⟨k₂, -, hk₂e⟩ := FixedDelay.request_step p w _ hw lookahead r b₂
  have hh₀ := Solution.handled_of_asked w (FixedDelay.solution p) lookahead hk₀e
  have hh₁ := Solution.handled_of_asked w (FixedDelay.solution p) lookahead hk₁e
  have hh₂ := Solution.handled_of_asked w (FixedDelay.solution p) lookahead hk₂e
  have ht₁ := Solution.handled_time w (FixedDelay.solution p) lookahead hh₁
  -- The estimate that the host remembers at request `b₁` was sent before it.
  obtain ⟨t₁, θ₁, -, ho₁, -, -⟩ := FixedDelay.offset_recent p w _ hw lookahead hsender hcopies
    hperiod hhs hh₀ (k := k₁) (by rw [ht₁]; exact hb₁)
  obtain ⟨s₁, s₂, s₄, hs₁, hs₄, hd₁, -, hd₂, -, -⟩ :=
    FixedDelay.offset_sample p w _ hw lookahead hsender hhs ho₁
  have hd₁' : d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender ≤ s₂ - s₁ := hd₁
  have hd₂' : d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r) ≤ s₄ - s₂ := hd₂
  have hlt₁ : t₁ < (w.clock (w.host r)).read ((w.speaker r).asked b₁) := by
    rw [← hs₁]
    apply (w.clock (w.host r)).strictMono
    rw [ht₁] at hs₄
    linarith
  -- The estimate that it remembers at step `n` was sent after request `b₁`.
  obtain ⟨t₂, θ₂, s', ho₂, hle₂, hs'⟩ := FixedDelay.offset_recent p w _ hw lookahead hsender
    hcopies hperiod hhs hh₂ (k := n) hn
  have hs'' : (w.speaker r).asked b₂ - p.period / (1 - ε) ≤ s' := hs'
  have hlt₂ : (w.clock (w.host r)).read ((w.speaker r).asked b₁) < t₂ := by
    refine lt_of_lt_of_le ((w.clock (w.host r)).strictMono ?_) hle₂
    linarith
  -- Both answers are in the view at step `n`.
  have hns : w.host r ≠ p.sender := hsender ▸ hhs
  obtain ⟨e₁, he₁, i₁, u₁, F₁, hobs₁, -⟩ := FixedDelay.offset_received p (w.host r) hns _ ho₁
  obtain ⟨e₂, he₂, i₂, u₂, F₂, hobs₂, -⟩ := FixedDelay.offset_received p (w.host r) hns _ ho₂
  have hk₁n : k₁ ≤ n := by
    by_contra hcon
    have hmono := Solution.eventTime_mono w (FixedDelay.solution p) lookahead (not_le.mp hcon).le
    rw [ht₁] at hmono
    linarith
  obtain ⟨l, hl, -⟩ := Solution.views_append w (FixedDelay.solution p) lookahead hk₁n (w.host r)
  have he₁' : e₁ ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
      n).views (w.host r) := by
    rw [hl]
    exact List.mem_append_left _ he₁
  exact ⟨⟨t₁, u₁, e₁.reading⟩, plainExchangesOf_mem he₁' hobs₁, ⟨t₂, u₂, e₂.reading⟩,
    plainExchangesOf_mem he₂ hobs₂, (hlt₁.trans hlt₂).ne⟩

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


/-! ## The exact latency -/

/-- **A speaker of the controller plays at an exact latency.** Consider a
world with constant rates within `ε < 1 / 2` of one, a speaker `r` whose
host is not the sender's, estimators that are exact on undisturbed data, and
the level held at `L`. Suppose that the capture device's clock runs less
than twice as fast as the clock of the speaker's device, and that the level
exceeds the delivery margin. Then, from some output sample on, the speaker
plays continuously, and each output sample plays the sound captured exactly
the level divided by the rate of the sender's clock, plus the asymmetry of
the speaker's host, before the sample leaves. -/
theorem speaker_exact (hS : ConstantRates m f d w) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    {clockEst : ClockEstimator} (hclock : clockEst.Exact) {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (L : ℝ) (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) (r : Fin R)
    (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers)
    (hratio : Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    (hlat : ((((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate + m.lead) / (1 - ε)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
      < L / (1 + ε)) :
    ∃ K, ∀ k, K ≤ k →
      PlaysContinuously ((solution p clockEst deviceEst (constantLevel L) :
        Solution H R Payload).plays w lookahead r) k ∧
      ∃ x, (solution p clockEst deviceEst (constantLevel L) :
          Solution H R Payload).plays w lookahead r k = some x ∧
        w.captured x = (w.speaker r).out k
          - (L / Real.exp (d.logRate m.sender)
            + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) := by
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
  have hw := hS.withinBounds hε0 hε hrates hdevices
  have hw' := hw
  obtain ⟨-, -, hspk, -, -, -, hlead, -, -, -, -⟩ := hw'
  have hρw := w.rate_pos
  have hρ := m.rate_pos
  have hrs := Real.exp_pos (d.logRate m.sender)
  have hrh := Real.exp_pos (d.logRate (m.host r))
  have hgc := Real.exp_pos (d.deviceLogRate none)
  have hgr := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have hrsle : Real.exp (d.logRate m.sender) ≤ 1 + ε := by
    have := (abs_le.mp (hrates m.sender)).2
    linarith
  -- The level is not negative.
  have hL : 0 ≤ L := by
    have h1 : (0 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (1 : ℝ) ≤ m.blockSize := by exact_mod_cast m.blockSize_pos
    have hδ₁ := hS.delay_pos (m.host r) m.sender
    have hδ₂ := hS.delay_pos m.sender (m.host r)
    have h3 : 0 ≤ ((((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate + m.lead)
        / (1 - ε) :=
      div_nonneg (add_nonneg (div_nonneg (by linarith) hρ.le) m.lead_pos.le) (by linarith)
    by_contra hneg
    have h5 : L / (1 + ε) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (by linarith)
    linarith
  -- The position that each output sample plays.
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ, ∀ k, X k = m.rate * Real.exp (d.deviceLogRate none)
      * (Real.exp (d.logRate m.sender) * ((w.speaker r).out k
          - (L / Real.exp (d.logRate m.sender)
            + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2))
        + d.offset m.sender - f.captureStart) / Real.exp (d.logRate m.sender) :=
    ⟨_, fun _ => rfl⟩
  have hcapX : ∀ k, w.captured (X k) = (w.speaker r).out k
      - (L / Real.exp (d.logRate m.sender)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) := by
    intro k
    rw [hS.captured, hX]
    field_simp
    ring
  have hstepX : ∀ k, X (k + 1) - X k = Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) := by
    intro k
    rw [hX, hX, hS.out, hS.out]
    push_cast
    field_simp
    ring
  -- Late requests.
  obtain ⟨T₀, hT₀⟩ := exists_two_exchanges p hS hε0 hε hrates hdevices lookahead hsender hcopies
    hperiod r hhs
  obtain ⟨bmin, hbmin⟩ := PlaybackDevice.asked_unbounded hρw (hspk r)
    (rateBounds m f d ε hε0 hε hS.delay_pos).deviceRate_lt_one (hlead r)
    (max T₀ (w.source.handed 1
      + d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r)))
  obtain ⟨bK, hbK⟩ := PlaybackDevice.asked_unbounded hρw (hspk r)
    (rateBounds m f d ε hε0 hε hS.delay_pos).deviceRate_lt_one (hlead r)
    ((L / Real.exp (d.logRate m.sender)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2)
      + (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender))
  choose step hstepb hstepe using FixedDelay.request_step p w _ hw lookahead r
  choose blk hblk using FixedDelay.exists_block_of_sample (w.speaker r)
  have hfirst := (w.speaker r).first_strictMono
  have hmemblk : ∀ k, k ∈ (w.speaker r).block (blk k) := by
    intro k
    unfold PlaybackDevice.block
    rw [List.mem_range'_1]
    have := hblk k
    omega
  have hlateblk : ∀ b₀ k, (w.speaker r).first b₀ ≤ k → b₀ ≤ blk k := by
    intro b₀ k hk
    by_contra hlt
    rw [not_le] at hlt
    have := hfirst.monotone (Nat.lt_iff_add_one_le.mp hlt)
    have := (hblk k).2
    omega
  have htime : ∀ b, (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w
      lookahead (step b) = (w.speaker r).asked b := fun b =>
    Solution.handled_time w (FixedDelay.solution p) lookahead
      (Solution.handled_of_asked w (FixedDelay.solution p) lookahead (hstepe b))
  have hlate : ∀ b, bmin ≤ b →
      max T₀ (w.source.handed 1
          + d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r))
        < (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w lookahead
          (step b) := by
    intro b hb
    rw [htime]
    exact lt_of_lt_of_le hbmin ((w.speaker r).asked_strictMono.monotone hb)
  -- What the host has estimated at a late request, and the position that follows.
  have hpos : ∀ k, (w.speaker r).first (max bmin 1) ≤ k →
      position p
        (scheduleOf p deviceEst (constantLevel L) (w.host r)
          (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
              lookahead (step (blk k))).views (w.host r)
            ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (blk k)),
              .asked r ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))⟩]))
        (clockOf p clockEst (w.host r)
          (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
              lookahead (step (blk k))).views (w.host r)
            ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (blk k)),
              .asked r ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))⟩]))
        (deviceEst (playbackReports r
          (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
              lookahead (step (blk k))).views (w.host r)
            ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (blk k)),
              .asked r ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))⟩])))
        (((w.speaker r).block (blk k)).headD 0) ((w.speaker r).reported (blk k)) k
      = some (X k) := by
    intro k hk
    have hb₀ := hlateblk _ k hk
    have hbmin' : bmin ≤ blk k := le_trans (le_max_left _ _) hb₀
    have hb1 : 1 ≤ blk k := le_trans (le_max_right _ _) hb₀
    have hT := hlate (blk k) hbmin'
    have haskedNext : ((solution p clockEst deviceEst (constantLevel L) :
        Solution H R Payload).states w lookahead (step (blk k))).askedNext r = blk k := by
      rw [Solution.askedNext_forget w Payload.plain lookahead hmore (step (blk k))]
      exact hstepb (blk k)
    -- The device line.
    have hdl := playbackLine_exact hS hdev
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead hb1
      haskedNext
    -- The clock line.
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hT₀ (step (blk k)) (lt_of_le_of_lt (le_max_left _ _) hT)
    have hex : exchangesOf
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (blk k))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (blk k)),
            .asked r ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))⟩])
        = plainExchangesOf
          (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
            (step (blk k))).views (w.host r)) := by
      rw [exchangesOf_eq, List.map_append,
        Solution.views_forget w Payload.plain lookahead hmore (step (blk k)) (w.host r)]
      simp [plainExchangesOf, List.filterMap_append, Event.mapMsg, Observation.mapMsg]
    have hcl : clockOf p clockEst (w.host r)
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (blk k))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (blk k)),
            .asked r ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))⟩])
        = some ⟨((d.offset m.sender
              - Real.exp (d.logRate m.sender) / Real.exp (d.logRate (m.host r))
                * d.offset (m.host r)
              + Real.exp (d.logRate m.sender)
                * (d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender))
            + (d.offset m.sender
              - Real.exp (d.logRate m.sender) / Real.exp (d.logRate (m.host r))
                * d.offset (m.host r)
              - Real.exp (d.logRate m.sender)
                * (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)))) / 2,
          Real.exp (d.logRate m.sender) / Real.exp (d.logRate (m.host r))⟩ := by
      unfold clockOf
      rw [ite_eq_right hns, hex]
      refine hclock _ _ _ _ (fun x hx => ?_) ⟨x₁, hx₁, x₂, hx₂, hne⟩
      obtain ⟨s₁, e1, e2, e3⟩ := exchange_of_view p hS lookahead hsender hx
      rw [hS.clock, hhost] at e1 e3
      rw [hS.clock, hhost, hsend] at e2
      rw [hsend] at e3
      rw [e1, e2, e3]
      exact exchange_lines hrh.ne'
    -- The schedule: the header of a block from the second on.
    obtain ⟨i₁, hi₁, arr, F₁, -, hh₁⟩ := FixedDelay.block_handled p w _ hw lookahead hsender
      hnodup hcopies hh hhs (b := 1) (k := step (blk k))
      (lt_of_le_of_lt (le_max_right _ _) hT)
    have hf₁ := Solution.handled_forget w Payload.plain lookahead hmore i₁
    rw [hh₁] at hf₁
    obtain ⟨⟨h', t', obs'⟩, hσh, heq⟩ := Option.map_eq_some_iff.mp hf₁
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hobs⟩ := heq
    obtain ⟨c₁, hobs₁, hpl₁⟩ : ∃ c₁ : Payload, obs' = .received w.sender c₁ F₁
        ∧ c₁.plain = .block (w.source.first 1) (w.source.reported 1) := by
      cases obs' with
      | handed frames stamp => simp [Observation.mapMsg] at hobs
      | asked r' outputs stamp => simp [Observation.mapMsg] at hobs
      | timer => simp [Observation.mapMsg] at hobs
      | received j c' F' =>
        simp only [Observation.mapMsg, Observation.received.injEq] at hobs
        obtain ⟨rfl, hpl, rfl⟩ := hobs
        exact ⟨c', rfl, hpl⟩
    obtain ⟨cp₁, pd₁, lv₁, sl₁, hc₁⟩ : ∃ cp₁ pd₁ lv₁ sl₁ : ℝ,
        c₁ = .block (w.source.first 1) (w.source.reported 1) cp₁ pd₁ lv₁ sl₁ := by
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
    obtain ⟨hd, hhd, hle⟩ := headerOf_latest _ hmem₁ rfl
    obtain ⟨e₂, he₂, j₂, st₂, F₂, hobs₂⟩ := headerOf_mem _ hhd
    obtain ⟨i₂, -, t₂, obs₂, hh₂, rfl⟩ := Solution.handled_of_mem_views w
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead he₂
    dsimp only at hobs₂
    subst hobs₂
    obtain ⟨msg, hmsg, -, -, -, hcont, -⟩ := Solution.handled_received w
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead hh₂
    obtain ⟨i₃, -, b₂, hh₃, hfr, -, hheader⟩ :=
      block_header w p clockEst deviceEst (constantLevel L) lookahead i₂ hmsg hcont
    have hb₂ : 1 ≤ b₂ := by
      rw [hfr] at hle
      exact w.source.first_strictMono.le_iff_le.mp hle
    have hline := captureLine_exact hS hdev
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload) lookahead hb₂ hh₃
    unfold blockHeader at hheader
    rw [hline] at hheader
    simp only [Option.map_some, Option.getD_some, Line.eval, constantLevel,
      Header.mk.injEq] at hheader
    obtain ⟨-, hcap, hper, hlev, hslo⟩ := hheader
    have hsched : scheduleOf p deviceEst (constantLevel L) (w.host r)
        (((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).states w
            lookahead (step (blk k))).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked (blk k)),
            .asked r ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))⟩])
        = some hd := by
      unfold scheduleOf
      rw [ite_eq_right hns, headerOf_append]
      exact hhd
    -- The position.
    rw [hsched, hcl, hdl]
    unfold position
    simp only [Option.map_some, Option.getD_some, Header.due, Line.eval]
    rw [hfr, hcap, hper, hlev, hslo, hX, hS.out]
    congr 1
    field_simp
    ring
  -- Late positions are past the start of the stream.
  have hX0 : ∀ k, (w.speaker r).first bK ≤ k → 0 ≤ X k := by
    intro k hk
    have hout := (w.speaker r).out_strictMono.monotone hk
    have hask := (w.speaker r).asked_before bK
    have h1 : (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
        ≤ (w.speaker r).out k
          - (L / Real.exp (d.logRate m.sender)
            + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) := by
      linarith
    have h2 := (div_le_iff₀ hrs).mp h1
    rw [hX]
    exact div_nonneg (mul_nonneg (mul_pos hρ hgc).le (by linarith)) hrs.le
  -- Late output samples play their positions.
  have hplays : ∀ k,
      max ((w.speaker r).first (max bmin 1)) ((w.speaker r).first bK) ≤ k →
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
        lookahead r k = some (X k) := by
    intro k hk
    have hk₀ := le_trans (le_max_left _ _) hk
    have hkK := le_trans (le_max_right _ _) hk
    have hb' : ((solution p clockEst deviceEst (constantLevel L) :
        Solution H R Payload).states w lookahead (step (blk k))).askedNext r = blk k := by
      rw [Solution.askedNext_forget w Payload.plain lookahead hmore (step (blk k))]
      exact hstepb (blk k)
    have he' : earliest (((solution p clockEst deviceEst (constantLevel L) :
          Solution H R Payload).states w lookahead (step (blk k))).key w)
        ((solution p clockEst deviceEst (constantLevel L) :
          Solution H R Payload).states w lookahead (step (blk k))).due
        = some (.asked r (blk k)) := by
      rw [(Solution.earliest_forget w Payload.plain lookahead hmore (step (blk k))).2]
      exact hstepe (blk k)
    rw [Solution.plays_of_asked_step w _ lookahead hb' he' (hmemblk k), plays_asked,
      hpos k hk₀, Solution.held_forget w Payload.plain lookahead hmore (step (blk k))]
    apply FixedDelay.playable_of_captured p w _ hw lookahead hsender hnodup hcopies hh hhs
      (hX0 k hkK)
    rw [hcapX, htime, hS.builds.rate_eq, hsend, hhost]
    -- The frames around the position arrived before the request.
    have hkb := hblk k
    have hout := (PlaybackDevice.out_sub_mem (hspk r) hkb.1).2
    rw [hS.builds.rate_eq] at hout
    have hask := (hlead r (blk k)).2
    have hsize : (w.speaker r).first (blk k + 1) = (w.speaker r).first (blk k) + m.blockSize := by
      rw [hS.builds.speaker_first, hS.builds.speaker_first]
      ring
    have hkg : (k : ℝ) - ((w.speaker r).first (blk k) : ℕ) ≤ (m.blockSize : ℝ) - 1 := by
      have h1 : k + 1 ≤ (w.speaker r).first (blk k) + m.blockSize := by omega
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ (((w.speaker r).first (blk k) + m.blockSize : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at h2
      linarith
    have hcoef : 0 ≤ (1 + ε / (1 - ε)) / m.rate :=
      div_nonneg (add_nonneg zero_le_one (div_nonneg hε0 (by linarith))) hρ.le
    have hout' : (w.speaker r).out k - (w.speaker r).out ((w.speaker r).first (blk k))
        ≤ (1 + ε / (1 - ε)) / m.rate * ((m.blockSize : ℝ) - 1) :=
      hout.trans (mul_le_mul_of_nonneg_left hkg hcoef)
    exact margin_arith hε hrsle hrs hL hlat hout' hask
  -- Late output samples play continuously.
  refine ⟨max ((w.speaker r).first (max bmin 1)) ((w.speaker r).first bK), fun k hk =>
    ⟨?_, X k, hplays k hk, hcapX k⟩⟩
  have hstep := hstepX k
  have hc0 : 0 < Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) := div_pos hgc hgr
  exact ⟨X k, X (k + 1), hplays k hk, hplays (k + 1) (le_trans hk (Nat.le_succ k)),
    by linarith, by linarith⟩

/-- **The controller plays at exact latencies when clocks and devices run at
constant rates.** Consider a world with constant rates within `ε < 1 / 2` of
one, in which no speaker is on the sender's host, estimators that are exact
on undisturbed data, and the level held at `L`. Suppose that the capture
device's clock runs less than twice as fast as the clock of every speaker's
device, and that the level exceeds the delivery margin of every speaker.
Then, from some output sample on, every output sample of each speaker plays
the sound captured exactly the level divided by the rate of the sender's
clock, plus the asymmetry of the speaker's host, before the sample leaves. -/
theorem playsAtLatencies (hS : ConstantRates m f d w) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    {clockEst : ClockEstimator} (hclock : clockEst.Exact) {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (L : ℝ) (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hratio : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    (hlat : ∀ r,
      ((((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate + m.lead) / (1 - ε)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
      < L / (1 + ε)) :
    ∃ K, w.PlaysAtLatencies
      ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
        lookahead)
      (fun r => L / Real.exp (d.logRate m.sender)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) K := by
  choose K hK using fun r => speaker_exact p hS hε0 hε hrates hdevices lookahead hclock hdev L
    hps hnodup hcopies hperiod r (hnos r) (hpsp r) (hratio r) (hlat r)
  exact ⟨Finset.univ.sup K, fun r k hk =>
    hK r k (le_trans (Finset.le_sup (Finset.mem_univ r)) hk)⟩


/-! ## The conditions of the theorem can be met -/

section Example

open MeasureTheory

/-- The example's model: three hosts, the sender and two speakers on their
own hosts and devices, devices at one frame per second in blocks of one
frame, a request lead of half a second, and shape two. -/
private def exampleModel : GenerativeWorld (Fin 3) 2 where
  rate := 1
  rate_pos := one_pos
  sender := 0
  host := ![1, 2]
  device := id
  device_idem := fun _ => rfl
  device_host := fun _ => rfl
  shape := 2
  shape_pos := two_pos
  blockSize := 1
  blockSize_pos := one_pos
  lead := 1 / 2
  lead_pos := by norm_num
  targetLatency := 3
  targetLatency_nonneg := by norm_num

/-- The example's member: round trips of one second, no pauses, no wander,
no spread of the clocks' mean rates and exact timestamps. -/
private def exampleMember : Member (Fin 3) 2 where
  roundTrip := fun _ _ => 1
  roundTrip_pos := fun _ _ => one_pos
  roundTrip_symm := fun _ _ => rfl
  linkPauseRate := fun _ _ => 0
  linkPauseRate_nonneg := fun _ _ => le_rfl
  linkPauseLength := fun _ _ => Measure.dirac 1
  linkPauseLength_prob := fun _ _ => inferInstance
  linkPauseLength_pos := fun _ _ => by simp
  linkPauseLength_mean := fun _ _ => integrable_dirac eNorm_lt_top
  linkLoad_lt_one := fun _ _ => by simp
  hostPauseRate := fun _ => 0
  hostPauseRate_nonneg := fun _ => le_rfl
  hostPauseLength := fun _ => Measure.dirac 1
  hostPauseLength_prob := fun _ => inferInstance
  hostPauseLength_pos := fun _ => by simp
  hostPauseLength_mean := fun _ => integrable_dirac eNorm_lt_top
  hostLoad_lt_one := fun _ => by simp
  rateSpread := 0
  rateSpread_nonneg := le_rfl
  wanderSize := fun _ => 0
  wanderSize_nonneg := fun _ => le_rfl
  wanderTime := fun _ => 1
  wanderTime_pos := fun _ => one_pos
  deviceWanderSize := fun _ => 0
  deviceWanderSize_nonneg := fun _ => le_rfl
  deviceWanderTime := fun _ => 1
  deviceWanderTime_pos := fun _ => one_pos
  reportSize := fun _ => 0
  reportSize_nonneg := fun _ => le_rfl
  reportTime := fun _ => 1
  reportTime_pos := fun _ => one_pos
  offsetRange := 1
  offsetRange_pos := one_pos
  captureStart := 0
  speakerStart := fun _ => 1

/-- The example's configuration: the sender sends the stream to both
speakers' hosts, each message once, and a host sends a clock query at most
once a second. -/
private def exampleParams : FixedDelay.Params (Fin 3) where
  sender := 0
  speakers := [1, 2]
  rate := 1
  latency := 3
  copies := 1
  period := 1
  slew := 1 / 2

/-- **The conditions of `playsAtLatencies` can be met.** There are a model, a
member, a world with constant rates and a configuration of the controller,
with the two-exchange and two-report estimators and the level held at three
seconds, that satisfy the conditions of the theorem; the controller
therefore plays at exact latencies in that world. In the example every clock
runs at the rate of true time, so it shows that the conditions are
consistent, and not that they hold in a world whose rates differ. -/
theorem playsAtLatencies_example :
    ∃ (m : GenerativeWorld (Fin 3) 2) (f : Member (Fin 3) 2) (d : Draw (Fin 3) 2)
      (w : World (Fin 3) 2) (p : FixedDelay.Params (Fin 3)) (K : ℕ),
      ConstantRates m f d w ∧
        w.PlaysAtLatencies
          ((solution p twoExchanges twoReports (constantLevel 3) :
            Solution (Fin 3) 2 Payload).plays w 1)
          (fun r => 3 / Real.exp (d.logRate m.sender)
            + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) K := by
  have hex : ∀ h : Fin 3, h = exampleModel.sender ∨ ∃ r, exampleModel.host r = h := by
    intro h
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  have hnos : ∀ r, exampleModel.host r ≠ exampleModel.sender := by
    intro r
    fin_cases r
    · show (1 : Fin 3) ≠ 0
      decide
    · show (2 : Fin 3) ≠ 0
      decide
  have hspeakers : ∀ r, exampleModel.host r ∈ exampleParams.speakers := by
    intro r
    fin_cases r
    · show (1 : Fin 3) ∈ [1, 2]
      decide
    · show (2 : Fin 3) ∈ [1, 2]
      decide
  have hnodup : exampleParams.speakers.Nodup := by
    show ([1, 2] : List (Fin 3)).Nodup
    decide
  obtain ⟨y, hy⟩ : ∃ y : Component (Fin 3) 2 → ℝ, y = fun _ => 1 / 2 := ⟨_, rfl⟩
  have hS : ConstantRates exampleModel exampleMember (canonicalDraw y)
      (canonicalWorld exampleModel exampleMember hex y) :=
    { builds := canonicalWorld_builds exampleModel exampleMember hex y
      no_wander := fun _ _ => rfl
      no_deviceWander := fun _ _ => rfl
      no_reportError := fun _ _ => rfl
      no_linkPauses := fun _ _ _ _ => rfl
      no_hostPauses := fun _ _ _ => rfl
      delay_pos := fun i j =>
        mul_pos (canonicalDraw_split_mem y i j).1 (exampleMember.roundTrip_pos i j) }
  have hrates : ∀ h, |Real.exp ((canonicalDraw y).logRate h) - 1| ≤ (0 : ℝ) := fun h => by
    simp [canonicalDraw]
  have hdevices : ∀ x, |Real.exp ((canonicalDraw y).deviceLogRate x) - 1| ≤ (0 : ℝ) :=
    fun x => by simp [canonicalDraw]
  obtain ⟨K, hK⟩ := playsAtLatencies exampleParams hS le_rfl (by norm_num) hrates hdevices 1
    twoExchanges_exact twoReports_exact 3 rfl hnodup Nat.one_pos zero_le_one hnos hspeakers
    (fun r => by simp [canonicalDraw])
    (fun r => by
      have hsw := canonicalDraw_split_swap y exampleModel.sender (exampleModel.host r)
      show ((((1 : ℕ) : ℝ) + 2 * (((1 : ℕ) : ℝ) - 1)) / 1 + 1 / 2) / (1 - 0)
          + ((canonicalDraw y).split exampleModel.sender (exampleModel.host r) * 1
            + (canonicalDraw y).split (exampleModel.host r) exampleModel.sender * 1) / 2
        < 3 / (1 + 0)
      norm_num
      linarith)
  exact ⟨exampleModel, exampleMember, canonicalDraw y, canonicalWorld exampleModel
    exampleMember hex y, exampleParams, K, hS, hK⟩

end Example

end Unisono.Solutions.Controller
