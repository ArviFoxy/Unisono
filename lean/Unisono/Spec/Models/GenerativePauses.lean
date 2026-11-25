/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeCanonical
public import Unisono.Spec.Models.GenerativeDelivery
public import Unisono.Spec.Models.GenerativeRates
public import Unisono.Spec.Models.PauseProcess
public import Mathlib.Probability.StrongLaw

/-!
# A random world with pauses

Every member of the generative model whose clocks do not wander and whose
audio devices report exact timestamps has a random world, with any number of
hosts and speakers (`exists_holds_of_steadyClocks`). Its links and its hosts
may pause, at any rates and with any laws of the lengths, and the mean rates
of its clocks may be spread.

The world of one draw:

* `Tame`: the paused time of a link or of a host leaves a finite backlog.
  The backlog at a true time is then a least upper bound, as `IsBacklog`
  asks (`isBacklog_backlog`).
* `Draw.Steady`: a draw without wander and without errors of the reports,
  whose paused times never decrease and are tame.
* `handledAt`: when a host handles an event that occurs at a true time,
  which is after its backlog at that time. It is no earlier than the event
  (`le_handledAt`) and never decreases (`handledAt_mono`).
* `drawWorld`: the world of a steady draw, which is the world built from the
  draw (`drawWorld_builds`). Each clock runs at its own constant rate, a
  message waits for the backlogs of the sending host, of the link and of the
  receiving host, and a host handles the events of its audio devices after
  its backlog. When no host pauses, the world has clocks at constant rates
  in the sense of `ConstantRates` (`drawWorld_constantRates`).

The paused time of the process of pauses (`pausedPath`) is tame in almost
every outcome:

* `integral_cellTotal`: the mean of the total length of the pauses that
  begin in one second is the rate of the pauses times the mean length of a
  pause.
* `ae_tame_pausedPath`: when that product is below one, the paused time is
  tame in almost every outcome, by the strong law of large numbers.
* `tamePath`: the paused time of an outcome, with no pause at all in the
  outcomes in which `pausedPath` is not tame, so that every outcome has a
  world. It has the law and the independence that the model asks for
  (`hasLaw_tamePath_sub`, `hasIndepIncrements_tamePath`).

The random world:

* `Member.SteadyClocks`: the members that the construction covers.
* `Member.SteadyHosts`: the members with steady clocks whose hosts never
  pause. In every random world of such a member, almost every outcome is a
  world with clocks at constant rates (`Prior.ae_constantRates`).
* `Component.Coordinate`, `steadyLaw`, `steadyDraw`: the probability space.
  An outcome has one coordinate for each component of a draw, and the
  coordinates are independent. The coordinate of a paused time is what is
  drawn for the cells of the process of pauses, and every other coordinate is
  one number. The draw of an outcome has the law of the member
  (`steadyDraw_prior`).
* `steadyWorld`: the world of an outcome, built from the draw of the outcome
  (`steadyWorld_builds`).
* `exists_holds_with_pauses`: an example of a member in which every link and
  every host pauses, with its random world.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## Paused time that leaves a finite backlog -/

/-- The paused time `X` leaves a finite backlog: the paused time that began
in the `n` seconds before true time zero exceeds `n` seconds by a bounded
amount, whatever `n` is. -/
def Tame (X : Time → ℝ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, X 0 - X (-(n : ℝ)) - n ≤ B

/-- When the paused time never decreases and is tame, the paused time that
began since any earlier true time exceeds the time since then by a bounded
amount. -/
theorem Tame.bddAbove {X : Time → ℝ} (h : Tame X) (hmono : Monotone X) (t : Time) :
    BddAbove {x | ∃ s ≤ t, x = X t - X s - (t - s)} := by
  obtain ⟨B, hB⟩ := h
  refine ⟨X t - X 0 + B + max 0 t + 1 - t, ?_⟩
  rintro x ⟨s, hs, rfl⟩
  have hn := hB ⌈-s⌉₊
  have h1 : -(⌈-s⌉₊ : ℝ) ≤ s := by
    have := Nat.le_ceil (-s)
    linarith
  have h2 := hmono h1
  have h3 : (⌈-s⌉₊ : ℝ) + s ≤ max 0 s + 1 := by
    rcases le_or_gt 0 (-s) with hneg | hpos
    · have h4 := Nat.ceil_lt_add_one hneg
      have h5 := le_max_left 0 s
      linarith
    · have hz : ⌈-s⌉₊ = 0 := Nat.ceil_eq_zero.mpr hpos.le
      have h5 := le_max_right 0 s
      rw [hz]
      push_cast
      linarith
  have h4 : max 0 s ≤ max 0 t := max_le_max le_rfl hs
  linarith

/-- **The backlog of a tame paused time exists**, at every true time. -/
theorem isBacklog_backlog {X : Time → ℝ} (h : Tame X) (hmono : Monotone X) (t : Time) :
    IsBacklog X t (backlog X t) :=
  isLUB_csSup ⟨0, t, le_rfl, by simp⟩ (h.bddAbove hmono t)

/-- When a host whose paused time is recorded by `X` handles an event that
occurs at true time `t`: after its backlog at `t`. -/
def handledAt (X : Time → ℝ) (t : Time) : Time :=
  t + backlog X t

/-- A host handles an event when it occurs, or later. -/
theorem le_handledAt {X : Time → ℝ} (h : Tame X) (hmono : Monotone X) (t : Time) :
    t ≤ handledAt X t :=
  le_add_of_nonneg_right (isBacklog_backlog h hmono t).nonneg

/-- A host handles its events in the order in which they occur: the true
time at which it handles an event never decreases with the true time of the
event. Events that occur during one pause are handled together when the
pause ends. -/
theorem handledAt_mono {X : Time → ℝ} (h : Tame X) (hmono : Monotone X) :
    Monotone (handledAt X) := fun _ _ hst =>
  (isBacklog_backlog h hmono _).add_le_add hmono (isBacklog_backlog h hmono _) hst

/-! ## The world of a draw with steady clocks -/

/-- A draw with steady clocks: no clock wanders, the audio devices report
exact timestamps, and the paused times of the links and of the hosts never
decrease and are tame. The mean rates of the clocks are arbitrary. -/
structure Draw.Steady (d : Draw H R) : Prop where
  split_mem : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1
  no_wander : ∀ h t, d.wander h t = 0
  no_deviceWander : ∀ x t, d.deviceWander x t = 0
  no_reportError : ∀ x t, d.reportError x t = 0
  linkPaused_monotone : ∀ i j, Monotone (d.linkPaused i j)
  hostPaused_monotone : ∀ h, Monotone (d.hostPaused h)
  linkPaused_tame : ∀ i j, Tame (d.linkPaused i j)
  hostPaused_tame : ∀ h, Tame (d.hostPaused h)

namespace Draw.Steady

variable {d : Draw H R}

/-- Each clock reads its offset plus its rate times true time. -/
theorem reading (hd : d.Steady) (h : H) (t : Time) :
    d.reading h t = d.offset h + Real.exp (d.logRate h) * t := by
  simp only [Draw.reading, hd.no_wander, add_zero, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]
  ring

/-- The clock of each audio device advances at a constant rate. -/
theorem deviceReading (hd : d.Steady) (x : Option (Fin R)) (t : Time) :
    d.deviceReading x t = Real.exp (d.deviceLogRate x) * t := by
  simp only [Draw.deviceReading, hd.no_deviceWander, add_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  ring

/-- Every message arrives after it is sent. -/
theorem lt_arrival (hd : d.Steady) (f : Member H R) (i j : H) (s : Time) :
    s < d.arrival f i j s := by
  have h1 := (isBacklog_backlog (hd.hostPaused_tame i) (hd.hostPaused_monotone i) s).nonneg
  have h2 := (isBacklog_backlog (hd.linkPaused_tame i j) (hd.linkPaused_monotone i j)
    (s + backlog (d.hostPaused i) s)).nonneg
  have h3 := (isBacklog_backlog (hd.hostPaused_tame j) (hd.hostPaused_monotone j)
    (s + backlog (d.hostPaused i) s + d.split i j * f.roundTrip i j
      + backlog (d.linkPaused i j) (s + backlog (d.hostPaused i) s))).nonneg
  have h4 := mul_pos (hd.split_mem i j).1 (f.roundTrip_pos i j)
  unfold Draw.arrival
  linarith

end Draw.Steady

theorem exp_mul_exp_neg (c : ℝ) : Real.exp c * Real.exp (-c) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- **The world of a draw with steady clocks.** The clock of a host reads
its offset plus its rate times true time. A device starts when the clock of
its host reads the member's start, and then runs at the rate of its own
clock. A message waits for the backlog of the sending host, then takes the
least delay of its direction and waits for the backlog of the link, and then
waits for the backlog of the receiving host. A host handles the handovers
and the requests of its audio devices after its backlog. -/
def drawWorld (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (d : Draw H R) (hd : d.Steady) :
    World H R where
  rate := m.rate
  rate_pos := m.rate_pos
  sender := m.sender
  host := m.host
  hosts := hex
  clock := fun h =>
    { read := fun t => d.offset h + Real.exp (d.logRate h) * t
      strictMono := fun a b hab => by
        have := mul_lt_mul_of_pos_left hab (Real.exp_pos (d.logRate h))
        linarith
      continuous := by fun_prop }
  source :=
    { capture := fun n =>
        (f.captureStart - d.offset m.sender) * Real.exp (-d.logRate m.sender)
          + (n : ℝ) / m.rate * Real.exp (-d.deviceLogRate none)
      capture_strictMono := fun a b hab => by
        have h1 : (a : ℝ) / m.rate < (b : ℝ) / m.rate :=
          div_lt_div_of_pos_right (Nat.cast_lt.mpr hab) m.rate_pos
        have := mul_lt_mul_of_pos_right h1 (Real.exp_pos (-d.deviceLogRate none))
        linarith
      first := fun b => b * m.blockSize
      first_zero := Nat.zero_mul _
      first_strictMono := fun _ _ hab => Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
      handed := fun b => handledAt (d.hostPaused m.sender)
        ((f.captureStart - d.offset m.sender) * Real.exp (-d.logRate m.sender)
          + (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate none))
      handed_mono := fun a b hab => by
        refine handledAt_mono (hd.hostPaused_tame _) (hd.hostPaused_monotone _) ?_
        have hle : (a + 1) * m.blockSize - 1 ≤ (b + 1) * m.blockSize - 1 :=
          Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (Nat.succ_le_succ hab)) 1
        have h1 : (((a + 1) * m.blockSize - 1 : ℕ) : ℝ) / m.rate
            ≤ (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) / m.rate :=
          div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) m.rate_pos.le
        have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-d.deviceLogRate none)).le
        linarith
      handed_after := fun _ => le_handledAt (hd.hostPaused_tame _) (hd.hostPaused_monotone _) _
      reported := fun b =>
        f.captureStart + Real.exp (d.logRate m.sender)
          * (((b * m.blockSize : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate none)) }
  speaker := fun r =>
    { out := fun k =>
        (f.speakerStart (m.device r) - d.offset (m.host r)) * Real.exp (-d.logRate (m.host r))
          + (k : ℝ) / m.rate * Real.exp (-d.deviceLogRate (some (m.device r)))
      out_strictMono := fun a b hab => by
        have h1 : (a : ℝ) / m.rate < (b : ℝ) / m.rate :=
          div_lt_div_of_pos_right (Nat.cast_lt.mpr hab) m.rate_pos
        have := mul_lt_mul_of_pos_right h1
          (Real.exp_pos (-d.deviceLogRate (some (m.device r))))
        linarith
      first := fun b => b * m.blockSize
      first_zero := Nat.zero_mul _
      first_strictMono := fun _ _ hab => Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
      asked := fun b => handledAt (d.hostPaused (m.host r))
        ((f.speakerStart (m.device r) - d.offset (m.host r)) * Real.exp (-d.logRate (m.host r))
          + (((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead)
            * Real.exp (-d.deviceLogRate (some (m.device r))))
      asked_mono := fun a b hab => by
        refine handledAt_mono (hd.hostPaused_tame _) (hd.hostPaused_monotone _) ?_
        have hle : a * m.blockSize ≤ b * m.blockSize := Nat.mul_le_mul_right _ hab
        have h1 : ((a * m.blockSize : ℕ) : ℝ) / m.rate ≤ ((b * m.blockSize : ℕ) : ℝ) / m.rate :=
          div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) m.rate_pos.le
        have := mul_le_mul_of_nonneg_right (show ((a * m.blockSize : ℕ) : ℝ) / m.rate - m.lead
            ≤ ((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead by linarith)
          (Real.exp_pos (-d.deviceLogRate (some (m.device r)))).le
        linarith
      reported := fun b =>
        f.speakerStart (m.device r) + Real.exp (d.logRate (m.host r))
          * (((b * m.blockSize : ℕ) : ℝ) / m.rate
            * Real.exp (-d.deviceLogRate (some (m.device r)))) }
  network :=
    { deliver := fun i j s _ => some (d.arrival f i j s)
      after := fun i j s _ a h => by
        simp only [Option.some.injEq] at h
        rw [← h]
        exact hd.lt_arrival f i j s }
  target := fun _ => m.targetLatency

/-- **The world of a draw with steady clocks is the world built from the
draw.** -/
theorem drawWorld_builds (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (d : Draw H R) (hd : d.Steady) :
    m.Builds f d (drawWorld m f hex d hd) where
  rate_eq := rfl
  sender_eq := rfl
  host_eq := rfl
  clock := fun h t => (hd.reading h t).symm
  network := fun i j s q =>
    ⟨backlog (d.hostPaused i) s, backlog (d.linkPaused i j) (s + backlog (d.hostPaused i) s),
      backlog (d.hostPaused j) (s + backlog (d.hostPaused i) s + d.split i j * f.roundTrip i j
        + backlog (d.linkPaused i j) (s + backlog (d.hostPaused i) s)),
      isBacklog_backlog (hd.hostPaused_tame i) (hd.hostPaused_monotone i) _,
      isBacklog_backlog (hd.linkPaused_tame i j) (hd.linkPaused_monotone i j) _,
      isBacklog_backlog (hd.hostPaused_tame j) (hd.hostPaused_monotone j) _, rfl⟩
  deviceClock := fun x =>
    ⟨{ read := fun t => Real.exp (d.deviceLogRate x) * t
       strictMono := fun a b hab => mul_lt_mul_of_pos_left hab (Real.exp_pos _)
       continuous := by fun_prop }, fun t => (hd.deviceReading x t).symm⟩
  capture_start := by
    have h := exp_mul_exp_neg (d.logRate m.sender)
    show d.offset m.sender + Real.exp (d.logRate m.sender)
        * ((f.captureStart - d.offset m.sender) * Real.exp (-d.logRate m.sender)
          + ((0 : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate none)) = f.captureStart
    push_cast
    linear_combination (f.captureStart - d.offset m.sender) * h
  capture := fun n => by
    have hg := exp_mul_exp_neg (d.deviceLogRate none)
    rw [hd.deviceReading, hd.deviceReading]
    show Real.exp (d.deviceLogRate none)
          * ((f.captureStart - d.offset m.sender) * Real.exp (-d.logRate m.sender)
            + (n : ℝ) / m.rate * Real.exp (-d.deviceLogRate none))
        - Real.exp (d.deviceLogRate none)
          * ((f.captureStart - d.offset m.sender) * Real.exp (-d.logRate m.sender)
            + ((0 : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate none))
      = (n : ℝ) / m.rate
    push_cast
    linear_combination ((n : ℝ) / m.rate) * hg
  capture_first := fun _ => rfl
  capture_handed := fun _ =>
    ⟨_, isBacklog_backlog (hd.hostPaused_tame _) (hd.hostPaused_monotone _) _, rfl⟩
  capture_reported := fun b => by
    have h := exp_mul_exp_neg (d.logRate m.sender)
    rw [hd.no_reportError]
    show f.captureStart + Real.exp (d.logRate m.sender)
          * (((b * m.blockSize : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate none))
      = d.offset m.sender + Real.exp (d.logRate m.sender)
          * ((f.captureStart - d.offset m.sender) * Real.exp (-d.logRate m.sender)
            + ((b * m.blockSize : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate none)) + 0
    linear_combination (-(f.captureStart - d.offset m.sender)) * h
  speaker_start := fun r => by
    have h := exp_mul_exp_neg (d.logRate (m.host r))
    show d.offset (m.host r) + Real.exp (d.logRate (m.host r))
        * ((f.speakerStart (m.device r) - d.offset (m.host r))
            * Real.exp (-d.logRate (m.host r))
          + ((0 : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate (some (m.device r))))
      = f.speakerStart (m.device r)
    push_cast
    linear_combination (f.speakerStart (m.device r) - d.offset (m.host r)) * h
  speaker_out := fun r k => by
    have hg := exp_mul_exp_neg (d.deviceLogRate (some (m.device r)))
    rw [hd.deviceReading, hd.deviceReading]
    show Real.exp (d.deviceLogRate (some (m.device r)))
          * ((f.speakerStart (m.device r) - d.offset (m.host r))
              * Real.exp (-d.logRate (m.host r))
            + (k : ℝ) / m.rate * Real.exp (-d.deviceLogRate (some (m.device r))))
        - Real.exp (d.deviceLogRate (some (m.device r)))
          * ((f.speakerStart (m.device r) - d.offset (m.host r))
              * Real.exp (-d.logRate (m.host r))
            + ((0 : ℕ) : ℝ) / m.rate * Real.exp (-d.deviceLogRate (some (m.device r))))
      = (k : ℝ) / m.rate
    push_cast
    linear_combination ((k : ℝ) / m.rate) * hg
  speaker_first := fun _ _ => rfl
  speaker_asked := fun r b => by
    refine ⟨_, _, ?_,
      isBacklog_backlog (hd.hostPaused_tame _) (hd.hostPaused_monotone _) _, rfl⟩
    have hg := exp_mul_exp_neg (d.deviceLogRate (some (m.device r)))
    rw [hd.deviceReading, hd.deviceReading]
    show Real.exp (d.deviceLogRate (some (m.device r)))
          * ((f.speakerStart (m.device r) - d.offset (m.host r))
              * Real.exp (-d.logRate (m.host r))
            + ((b * m.blockSize : ℕ) : ℝ) / m.rate
              * Real.exp (-d.deviceLogRate (some (m.device r))))
        - Real.exp (d.deviceLogRate (some (m.device r)))
          * ((f.speakerStart (m.device r) - d.offset (m.host r))
              * Real.exp (-d.logRate (m.host r))
            + (((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead)
              * Real.exp (-d.deviceLogRate (some (m.device r))))
      = m.lead
    linear_combination m.lead * hg
  speaker_reported := fun r b => by
    have h := exp_mul_exp_neg (d.logRate (m.host r))
    rw [hd.no_reportError]
    show f.speakerStart (m.device r) + Real.exp (d.logRate (m.host r))
          * (((b * m.blockSize : ℕ) : ℝ) / m.rate
            * Real.exp (-d.deviceLogRate (some (m.device r))))
      = d.offset (m.host r) + Real.exp (d.logRate (m.host r))
          * ((f.speakerStart (m.device r) - d.offset (m.host r))
              * Real.exp (-d.logRate (m.host r))
            + ((b * m.blockSize : ℕ) : ℝ) / m.rate
              * Real.exp (-d.deviceLogRate (some (m.device r)))) + 0
    linear_combination (-(f.speakerStart (m.device r) - d.offset (m.host r))) * h
  target_eq := fun _ => rfl

/-- The world of a draw with steady clocks in which no host pauses has
clocks at constant rates, in the sense of `ConstantRates`. -/
theorem drawWorld_constantRates (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (d : Draw H R) (hd : d.Steady)
    (hhost : ∀ h s t, d.hostPaused h s = d.hostPaused h t) :
    ConstantRates m f d (drawWorld m f hex d hd) where
  builds := drawWorld_builds m f hex d hd
  no_wander := hd.no_wander
  no_deviceWander := hd.no_deviceWander
  no_reportError := hd.no_reportError
  delay_pos := fun i j => mul_pos (hd.split_mem i j).1 (f.roundTrip_pos i j)
  linkPaused_monotone := hd.linkPaused_monotone
  no_hostPauses := hhost

/-! ## Almost surely the paused time is tame -/

/-- The mean of a number with the Poisson law is its parameter. -/
theorem hasSum_natCast_poisson (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) r := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  convert (hasSum_one_poissonMeasure r).mul_left (r : ℝ) using 1
  · funext k
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · simp

/-- The mean, as a lower integral, of a number with the Poisson law. -/
theorem lintegral_natCast_poisson (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r = ENNReal.ofReal r := by
  have hsum := hasSum_natCast_poisson r
  rw [lintegral_countable']
  have hterm : ∀ n : ℕ, (n : ℝ≥0∞) * poissonMeasure r {n}
      = ENNReal.ofReal (Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
    intro n
    rw [poissonMeasure_singleton, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      mul_comm]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq]

/-- **The mean of the sum of a function over the pauses of a cell**, as a
lower integral: the rate times the mean of the function for one pause. -/
theorem lintegral_cellSum (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫⁻ cell, ENNReal.ofReal (cellSum g cell) ∂cellLaw rate F
      = ENNReal.ofReal rate * ∫⁻ z, ENNReal.ofReal (g z) ∂markLaw F := by
  have hmeas : Measurable fun cell : Cell => ENNReal.ofReal (cellSum g cell) :=
    ENNReal.measurable_ofReal.comp (measurable_cellSum hg)
  unfold cellLaw
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ n : ℕ, ∫⁻ ξ : ℕ → ℝ × ℝ, ENNReal.ofReal (cellSum g (n, ξ))
        ∂Measure.infinitePi (fun _ : ℕ => markLaw F)
      = (n : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (g z) ∂markLaw F := by
    intro n
    have hone : ∀ k : ℕ, ∫⁻ ξ : ℕ → ℝ × ℝ, ENNReal.ofReal (g (ξ k))
          ∂Measure.infinitePi (fun _ : ℕ => markLaw F)
        = ∫⁻ z, ENNReal.ofReal (g z) ∂markLaw F := by
      intro k
      have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => markLaw F) k
      calc ∫⁻ ξ : ℕ → ℝ × ℝ, ENNReal.ofReal (g (ξ k))
            ∂Measure.infinitePi (fun _ : ℕ => markLaw F)
          = ∫⁻ z, ENNReal.ofReal (g z)
              ∂(Measure.infinitePi fun _ : ℕ => markLaw F).map (fun ξ => ξ k) :=
            (lintegral_map (ENNReal.measurable_ofReal.comp hg) (measurable_pi_apply k)).symm
        _ = ∫⁻ z, ENNReal.ofReal (g z) ∂markLaw F := by rw [hmap]
    have hsum : ∀ ξ : ℕ → ℝ × ℝ, ENNReal.ofReal (cellSum g (n, ξ))
        = ∑ k ∈ Finset.range n, ENNReal.ofReal (g (ξ k)) := fun ξ =>
      ENNReal.ofReal_sum_of_nonneg fun k _ => hg0 _
    simp_rw [hsum]
    rw [lintegral_finsetSum (f := fun k (ξ : ℕ → ℝ × ℝ) => ENNReal.ofReal (g (ξ k))) _
      fun k _ => ENNReal.measurable_ofReal.comp (hg.comp (measurable_pi_apply k))]
    rw [Finset.sum_congr rfl fun k _ => hone k, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  simp_rw [hinner]
  rw [lintegral_mul_const _ Measurable.of_discrete, lintegral_natCast_poisson]

/-- The lengths of all pauses of a cell, added up. -/
def cellTotal (cell : Cell) : ℝ := cellSum (fun z => max z.2 0) cell

theorem measurable_cellTotal : Measurable cellTotal :=
  measurable_cellSum (measurable_snd.max measurable_const)

theorem cellTotal_nonneg (cell : Cell) : 0 ≤ cellTotal cell :=
  cellSum_nonneg (fun _ => le_max_right _ _) cell

theorem cellSum_le_cellTotal {h : ℝ × ℝ → ℝ} (hh : ∀ z, h z ≤ max z.2 0) (cell : Cell) :
    cellSum h cell ≤ cellTotal cell :=
  Finset.sum_le_sum fun _ _ => hh _

/-- A length drawn from a law of positive lengths is almost surely not
negative. -/
theorem ae_nonneg_of_Iic {F : Measure ℝ} (hF : F (Set.Iic 0) = 0) :
    0 ≤ᵐ[F] fun x : ℝ => x := by
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hF
  show x ≤ 0
  exact (not_le.mp hx).le

/-- **The mean of the total length of the pauses of a cell**, as a lower
integral: the rate of the pauses times the mean length of a pause. -/
theorem lintegral_cellTotal (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) (hmean : Integrable (fun x : ℝ => x) F) :
    ∫⁻ cell, ENNReal.ofReal (cellTotal cell) ∂cellLaw rate F
      = ENNReal.ofReal (rate * ∫ x, x ∂F) := by
  have hmark : ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (max z.2 0) ∂markLaw F
      = ∫⁻ x, ENNReal.ofReal x ∂F := by
    unfold markLaw
    rw [lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const, measure_univ, mul_one]
    refine lintegral_congr fun x => ?_
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  unfold cellTotal
  rw [lintegral_cellSum rate F (g := fun z : ℝ × ℝ => max z.2 0)
      (measurable_snd.max measurable_const) fun _ => le_max_right _ _,
    hmark, ← ofReal_integral_eq_lintegral_ofReal hmean (ae_nonneg_of_Iic hF),
    ← ENNReal.ofReal_mul rate.coe_nonneg]

theorem integrable_cellTotal (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) (hmean : Integrable (fun x : ℝ => x) F) :
    Integrable cellTotal (cellLaw rate F) := by
  refine ⟨measurable_cellTotal.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall cellTotal_nonneg),
    lintegral_cellTotal rate F hF hmean]
  exact ENNReal.ofReal_lt_top

/-- **The mean of the total length of the pauses of a cell** is the rate of
the pauses times the mean length of a pause. -/
theorem integral_cellTotal (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) (hmean : Integrable (fun x : ℝ => x) F) :
    ∫ cell, cellTotal cell ∂cellLaw rate F = rate * ∫ x, x ∂F := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall cellTotal_nonneg)
    measurable_cellTotal.aestronglyMeasurable, lintegral_cellTotal rate F hF hmean,
    ENNReal.toReal_ofReal]
  exact mul_nonneg rate.coe_nonneg (integral_nonneg_of_ae (ae_nonneg_of_Iic hF))

theorem markIn_le (c : ℤ) (s t : ℝ) (z : ℝ × ℝ) : markIn c s t z ≤ max z.2 0 := by
  unfold markIn
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

/-- The paused time that begins in the `n` seconds before true time zero is
at most the total length of the pauses of the cells from `-n` to zero. -/
theorem pausedBetween_neg_le (n : ℕ) (ω : Cells) :
    pausedBetween (-(n : ℝ)) 0 ω ≤ ∑ k ∈ Finset.range (n + 1), cellTotal (ω (-(k : ℤ))) := by
  have hfloor : ⌊-(n : ℝ)⌋ = -(n : ℤ) := by rw [Int.floor_neg, Int.ceil_natCast]
  have hsub : Finset.Icc ⌊-(n : ℝ)⌋ ⌊(0 : ℝ)⌋
      ⊆ (Finset.range (n + 1)).image fun k : ℕ => -(k : ℤ) := by
    intro c hc
    rw [hfloor, Int.floor_zero, Finset.mem_Icc] at hc
    rw [Finset.mem_image]
    refine ⟨(-c).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    show -(((-c).toNat : ℕ) : ℤ) = c
    omega
  calc pausedBetween (-(n : ℝ)) 0 ω
      = ∑ c ∈ (Finset.range (n + 1)).image fun k : ℕ => -(k : ℤ),
          cellSum (markIn c (-(n : ℝ)) 0) (ω c) := pausedBetween_eq_sum hsub ω
    _ ≤ ∑ c ∈ (Finset.range (n + 1)).image fun k : ℕ => -(k : ℤ), cellTotal (ω c) :=
        Finset.sum_le_sum fun c _ => cellSum_le_cellTotal (markIn_le c _ _) _
    _ = ∑ k ∈ Finset.range (n + 1), cellTotal (ω (-(k : ℤ))) :=
        Finset.sum_image fun a _ b _ h => by simpa using h

/-- **Almost surely the paused time leaves a finite backlog**, when the
pauses take less than all of the time on average: the rate of the pauses
times the mean length of a pause is below one. The total lengths of the
pauses of the cells are independent and have one law, so by the strong law of
large numbers the paused time that began in the `n` seconds before true time
zero is below `n` seconds for every large `n`. -/
theorem ae_tame_pausedPath (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) (hmean : Integrable (fun x : ℝ => x) F)
    (hload : rate * ∫ x, x ∂F < 1) :
    ∀ᵐ ω ∂cellsLaw rate F, Tame (pausedPath ω) := by
  -- The total length of the pauses of cell `-k`, for each `k`.
  let Y : ℕ → Cells → ℝ := fun k ω => cellTotal (ω (-(k : ℤ)))
  have hmeasY : ∀ k, Measurable (Y k) := fun k =>
    measurable_cellTotal.comp (measurable_pi_apply _)
  have heval : ∀ k : ℕ, (cellsLaw rate F).map (fun ω : Cells => ω (-(k : ℤ)))
      = cellLaw rate F := fun k =>
    Measure.infinitePi_map_eval (fun _ : ℤ => cellLaw rate F) (-(k : ℤ))
  have hmap : ∀ k, (cellsLaw rate F).map (Y k) = (cellLaw rate F).map cellTotal := by
    intro k
    calc (cellsLaw rate F).map (Y k)
        = ((cellsLaw rate F).map fun ω : Cells => ω (-(k : ℤ))).map cellTotal :=
          (Measure.map_map measurable_cellTotal (measurable_pi_apply _)).symm
      _ = (cellLaw rate F).map cellTotal := by rw [heval k]
  have hint : Integrable (Y 0) (cellsLaw rate F) := by
    have h := integrable_cellTotal rate F hF hmean
    rw [← heval 0] at h
    exact (integrable_map_measure measurable_cellTotal.aestronglyMeasurable
      (measurable_pi_apply _).aemeasurable).mp h
  have hmeanY : ∫ ω, Y 0 ω ∂cellsLaw rate F = rate * ∫ x, x ∂F := by
    rw [← integral_cellTotal rate F hF hmean]
    calc ∫ ω, Y 0 ω ∂cellsLaw rate F
        = ∫ cell, cellTotal cell
            ∂(cellsLaw rate F).map fun ω : Cells => ω (-((0 : ℕ) : ℤ)) :=
          (integral_map (φ := fun ω : Cells => ω (-((0 : ℕ) : ℤ)))
            (measurable_pi_apply _).aemeasurable
            measurable_cellTotal.aestronglyMeasurable).symm
      _ = ∫ cell, cellTotal cell ∂cellLaw rate F := by rw [heval 0]
  have hind : iIndepFun Y (cellsLaw rate F) :=
    (iIndepFun_infinitePi (P := fun _ : ℤ => cellLaw rate F) (X := fun _ => cellTotal)
      (fun _ => measurable_cellTotal)).precomp
        (g := fun k : ℕ => -(k : ℤ)) fun a b h => by simpa using h
  have hpair : Pairwise (Function.onFun (fun X₁ X₂ => IndepFun X₁ X₂ (cellsLaw rate F)) Y) :=
    fun i j hij => hind.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) (cellsLaw rate F) (cellsLaw rate F) := fun i =>
    ⟨(hmeasY i).aemeasurable, (hmeasY 0).aemeasurable, by rw [hmap i, hmap 0]⟩
  filter_upwards [strong_law_ae_real Y hint hpair hident] with ω hω
  rw [hmeanY] at hω
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hω).2 1 hload)
  refine ⟨⌈∑ i ∈ Finset.range (N + 1), Y i ω⌉₊ + 1, fun n => ?_⟩
  have hsub := pausedPath_sub (show -(n : ℝ) ≤ 0 by simp) ω
  have hle : pausedBetween (-(n : ℝ)) 0 ω ≤ ∑ i ∈ Finset.range (n + 1), Y i ω :=
    pausedBetween_neg_le n ω
  have hceil := Nat.le_ceil (∑ i ∈ Finset.range (N + 1), Y i ω)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  rcases le_or_gt N (n + 1) with hNn | hNn
  · have h1 := hN (n + 1) hNn
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_one hpos] at h1
    push_cast at h1
    have hc0 : (0 : ℝ) ≤ ⌈∑ i ∈ Finset.range (N + 1), Y i ω⌉₊ := Nat.cast_nonneg _
    linarith
  · have h1 : ∑ i ∈ Finset.range (n + 1), Y i ω ≤ ∑ i ∈ Finset.range (N + 1), Y i ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        fun i _ _ => cellTotal_nonneg _
    linarith

/-- The outcomes in which the paused time is tame form a measurable set. -/
theorem measurableSet_tame_pausedPath : MeasurableSet {ω : Cells | Tame (pausedPath ω)} := by
  have h : {ω : Cells | Tame (pausedPath ω)}
      = ⋃ B : ℕ, ⋂ n : ℕ, {ω : Cells | pausedPath ω 0 - pausedPath ω (-(n : ℝ)) - n ≤ B} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_iInter]
    rfl
  rw [h]
  exact MeasurableSet.iUnion fun B => MeasurableSet.iInter fun n =>
    measurableSet_le (((measurable_pausedPath 0).sub (measurable_pausedPath _)).sub
      measurable_const) measurable_const

/-! ## The paused time of every outcome -/

open Classical in
/-- The paused time of what is drawn for the cells: `pausedPath` if it is
tame, and no pause at all otherwise. Almost every outcome is of the first
kind (`tamePath_ae_eq`). The second kind is there so that every outcome has
backlogs, and with them a world. -/
def tamePath (ω : Cells) : Time → ℝ :=
  if Tame (pausedPath ω) then pausedPath ω else fun _ => 0

theorem tamePath_of_tame {ω : Cells} (h : Tame (pausedPath ω)) :
    tamePath ω = pausedPath ω := by
  unfold tamePath
  rw [ite_eq_left h]

theorem tamePath_monotone (ω : Cells) : Monotone (tamePath ω) := by
  unfold tamePath
  split_ifs
  · exact pausedPath_monotone ω
  · exact monotone_const

theorem tamePath_zero (ω : Cells) : tamePath ω 0 = 0 := by
  unfold tamePath
  split_ifs
  · exact pausedPath_zero ω
  · rfl

theorem tamePath_rightContinuous (ω : Cells) (t : Time) :
    ContinuousWithinAt (tamePath ω) (Set.Ici t) t := by
  unfold tamePath
  split_ifs
  · exact pausedPath_rightContinuous ω t
  · exact continuousWithinAt_const

theorem tamePath_tame (ω : Cells) : Tame (tamePath ω) := by
  unfold tamePath
  split_ifs with h
  · exact h
  · exact ⟨0, fun n => by simp⟩

theorem measurable_tamePath : Measurable tamePath := by
  classical
  refine measurable_pi_iff.mpr fun t => ?_
  have h : (fun ω : Cells => tamePath ω t)
      = fun ω => if Tame (pausedPath ω) then pausedPath ω t else 0 := by
    funext ω
    unfold tamePath
    split_ifs <;> rfl
  rw [h]
  exact Measurable.ite measurableSet_tame_pausedPath (measurable_pausedPath t) measurable_const

/-- In almost every outcome the paused time is the one of the process of
pauses, when the pauses take less than all of the time on average. -/
theorem tamePath_ae_eq (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) (hmean : Integrable (fun x : ℝ => x) F)
    (hload : rate * ∫ x, x ∂F < 1) :
    ∀ᵐ ω ∂cellsLaw rate F, tamePath ω = pausedPath ω := by
  filter_upwards [ae_tame_pausedPath rate F hF hmean hload] with ω hω
  exact tamePath_of_tame hω

/-- Independent random variables stay independent when they are read on
another probability space through a map that preserves the law. -/
theorem iIndepFun_of_measurePreserving {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {μ : Measure Ω}
    {μ' : Measure Ω'} {φ : Ω → Ω'} (hφ : MeasurePreserving φ μ μ') {g : ∀ i, Ω' → β i}
    (hg : ∀ i, Measurable (g i)) (h : iIndepFun g μ') :
    iIndepFun (fun i ω => g i (φ ω)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets H
  have hInter : (⋂ i ∈ S, (fun ω => g i (φ ω)) ⁻¹' sets i)
      = φ ⁻¹' (⋂ i ∈ S, g i ⁻¹' sets i) := by
    rw [Set.preimage_iInter₂]
    rfl
  rw [hInter, hφ.measure_preimage
    (Finset.measurableSet_biInter S fun i hi => hg i (H i hi)).nullMeasurableSet, h S H]
  refine Finset.prod_congr rfl fun i hi => ?_
  exact (hφ.measure_preimage (hg i (H i hi)).nullMeasurableSet).symm

section Cells

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Cells} {r : ℝ}
  {F : Measure ℝ} [IsProbabilityMeasure F]

/-- **The paused time that begins between two true times has the law
`pauseLaw`**, on any probability space on which what is drawn for the cells
has the law `cellsLaw`. -/
theorem hasLaw_tamePath_sub (hr : 0 ≤ r) (hF : F (Set.Iic 0) = 0)
    (hmean : Integrable (fun x : ℝ => x) F) (hload : r * ∫ x, x ∂F < 1)
    (hX : MeasurePreserving X P (cellsLaw (Real.toNNReal r) F)) {s t : ℝ} (hst : s ≤ t) :
    HasLaw (fun ω => tamePath (X ω) t - tamePath (X ω) s)
      (pauseLaw (Real.toNNReal (r * (t - s))) F) P := by
  have hload' : ((Real.toNNReal r : ℝ≥0) : ℝ) * ∫ x, x ∂F < 1 := by
    rwa [Real.coe_toNNReal r hr]
  have hcells : HasLaw (fun ω : Cells => tamePath ω t - tamePath ω s)
      (pauseLaw (Real.toNNReal (r * (t - s))) F) (cellsLaw (Real.toNNReal r) F) := by
    have h := hasLaw_pausedPath_sub (Real.toNNReal r) F hF hst
    rw [Real.coe_toNNReal r hr] at h
    refine h.congr ?_
    filter_upwards [tamePath_ae_eq (Real.toNNReal r) F hF hmean hload'] with ω hω
    rw [hω]
  exact hcells.fun_comp hX.hasLaw

/-- **The paused time that begins in periods that do not overlap is
independent**, on any probability space on which what is drawn for the cells
has the law `cellsLaw`. -/
theorem hasIndepIncrements_tamePath (hr : 0 ≤ r) (hF : F (Set.Iic 0) = 0)
    (hmean : Integrable (fun x : ℝ => x) F) (hload : r * ∫ x, x ∂F < 1)
    (hX : MeasurePreserving X P (cellsLaw (Real.toNNReal r) F)) :
    HasIndepIncrements (fun t ω => tamePath (X ω) t) P := by
  have hload' : ((Real.toNNReal r : ℝ≥0) : ℝ) * ∫ x, x ∂F < 1 := by
    rwa [Real.coe_toNNReal r hr]
  intro n t ht
  have hcells : iIndepFun (fun (i : Fin n) (ω : Cells) =>
      tamePath ω (t i.succ) - tamePath ω (t i.castSucc)) (cellsLaw (Real.toNNReal r) F) := by
    refine (iIndepFun_congr fun i => ?_).mp
      (hasIndepIncrements_pausedPath (Real.toNNReal r) F hF n t ht)
    filter_upwards [tamePath_ae_eq (Real.toNNReal r) F hF hmean hload'] with ω hω
    rw [hω]
  exact iIndepFun_of_measurePreserving hX
    (fun i : Fin n => (measurable_pi_iff.mp measurable_tamePath (t i.succ)).sub
      (measurable_pi_iff.mp measurable_tamePath (t i.castSucc))) hcells

end Cells

/-! ## The probability space -/

/-- A member has steady clocks: the clocks of its hosts and of its audio
devices do not wander, and its audio devices report exact timestamps. Its
links and its hosts may pause, and the mean rates of its clocks may be
spread. -/
structure Member.SteadyClocks (f : Member H R) : Prop where
  no_wander : ∀ h, f.wanderSize h = 0
  no_deviceWander : ∀ x, f.deviceWanderSize x = 0
  no_reportError : ∀ x, f.reportSize x = 0

/-- A noiseless member has steady clocks. -/
theorem Member.Noiseless.steadyClocks {f : Member H R} (hf : f.Noiseless) : f.SteadyClocks :=
  ⟨hf.no_wander, hf.no_deviceWander, hf.no_reportError⟩

/-- A member has steady hosts: it has steady clocks, and its hosts never
pause, so that every host handles the events of its audio devices when they
occur. Its links may pause, and the mean rates of its clocks may be
spread. -/
structure Member.SteadyHosts (f : Member H R) : Prop extends f.SteadyClocks where
  no_hostPauses : ∀ h, f.hostPauseRate h = 0

/-- A noiseless member has steady hosts. -/
theorem Member.Noiseless.steadyHosts {f : Member H R} (hf : f.Noiseless) : f.SteadyHosts :=
  ⟨hf.steadyClocks, hf.no_hostPauses⟩

/-- **A member with steady hosts draws worlds with clocks at constant
rates.** In every random world of such a member, almost every outcome is a
world in which no clock wanders, the audio devices report exact timestamps
and no host pauses (`ConstantRates`). -/
theorem Prior.ae_constantRates {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {m : GenerativeWorld H R} {f : Member H R} (hD : m.Prior f P D)
    (hf : f.SteadyHosts) {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω)) :
    ∀ᵐ ω ∂P, ConstantRates m f (D ω) (world ω) := by
  have := hD.prob
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have : Finite H := (world ω₀).finite_hosts
  have h1 : ∀ᵐ ω ∂P, ∀ h t, (D ω).wander h t = 0 :=
    ae_all_iff.mpr fun h => hD.wander_ae_eq_zero (hf.no_wander h)
  have h2 : ∀ᵐ ω ∂P, ∀ x t, (D ω).deviceWander x t = 0 :=
    ae_all_iff.mpr fun x => hD.deviceWander_ae_eq_zero (hf.no_deviceWander x)
  have h3 : ∀ᵐ ω ∂P, ∀ x t, (D ω).reportError x t = 0 :=
    ae_all_iff.mpr fun x => hD.reportError_ae_eq_zero (hf.no_reportError x)
  have h4 : ∀ᵐ ω ∂P, ∀ h s t, (D ω).hostPaused h s = (D ω).hostPaused h t :=
    ae_all_iff.mpr fun h => hD.hostPaused_ae_const (hf.no_hostPauses h)
  filter_upwards [h1, h2, h3, h4] with ω hw hdw herr hhost
  exact
    { builds := hB ω
      no_wander := hw
      no_deviceWander := hdw
      no_reportError := herr
      delay_pos := fun i j => hD.leastDelay_pos ω i j
      linkPaused_monotone := hD.linkPaused_monotone ω
      no_hostPauses := hhost }

/-- The coordinate of an outcome that belongs to each component of a draw:
what is drawn for the cells of the pauses, for the paused time of a link or
of a host, and one number for every other component. -/
def Component.Coordinate : Component H R → Type
  | .split _ => ℝ
  | .offset _ => ℝ
  | .logRate _ => ℝ
  | .wander _ => ℝ
  | .linkPaused _ _ => Cells
  | .hostPaused _ => Cells
  | .deviceLogRate _ => ℝ
  | .deviceWander _ => ℝ
  | .reportError _ => ℝ

instance (p : Component H R) : MeasurableSpace p.Coordinate := by
  cases p
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace Cells)
  · exact inferInstanceAs (MeasurableSpace Cells)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)

/-- The law of each coordinate: the Beta law for the split of a pair, the
uniform law for the offset of a clock, the Gaussian law for the logarithm of
the mean rate of a clock, the law of the cells of the pauses for the paused
time of a link or of a host, and zero for the wander and for the errors of
the reports, which a member with steady clocks does not have. -/
def steadyLaw (m : GenerativeWorld H R) (f : Member H R) :
    (p : Component H R) → Measure p.Coordinate
  | .split _ => (betaMeasure m.shape m.shape : Measure ℝ)
  | .offset _ =>
    (ProbabilityTheory.cond volume (Set.Icc (-f.offsetRange) f.offsetRange) : Measure ℝ)
  | .logRate _ => gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))
  | .wander _ => Measure.dirac (0 : ℝ)
  | .linkPaused i j => cellsLaw (Real.toNNReal (f.linkPauseRate i j)) (f.linkPauseLength i j)
  | .hostPaused h => cellsLaw (Real.toNNReal (f.hostPauseRate h)) (f.hostPauseLength h)
  | .deviceLogRate _ => gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))
  | .deviceWander _ => Measure.dirac (0 : ℝ)
  | .reportError _ => Measure.dirac (0 : ℝ)

instance (m : GenerativeWorld H R) (f : Member H R) (p : Component H R) :
    IsProbabilityMeasure (steadyLaw m f p) := by
  cases p with
  | split z => exact isProbabilityMeasureBeta m.shape_pos m.shape_pos
  | offset h =>
    have hpos : 0 < f.offsetRange - -f.offsetRange := by linarith [f.offsetRange_pos]
    have hprob : IsProbabilityMeasure
        (ProbabilityTheory.cond (volume : Measure ℝ)
          (Set.Icc (-f.offsetRange) f.offsetRange)) :=
      cond_isProbabilityMeasure_of_finite
        (by rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.mpr hpos).ne')
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    exact hprob
  | logRate h => exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 _))
  | wander h => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | linkPaused i j =>
    have := f.linkPauseLength_prob i j
    exact inferInstanceAs (IsProbabilityMeasure (cellsLaw _ (f.linkPauseLength i j)))
  | hostPaused h =>
    have := f.hostPauseLength_prob h
    exact inferInstanceAs (IsProbabilityMeasure (cellsLaw _ (f.hostPauseLength h)))
  | deviceLogRate x => exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 _))
  | deviceWander x => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | reportError x => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))

section Draw

variable [DecidableEq H]

/-- The numbers of an outcome that are drawn for the pairs of hosts. -/
def splitCoordinates (y : ∀ p : Component H R, p.Coordinate) : Component H R → ℝ
  | .split z => y (.split z)
  | _ => 0

/-- The draw of an outcome: the split of a pair, in its fixed order, the
offsets and the logarithms of the mean rates of the clocks of the hosts and
of the audio devices are coordinates of the outcome; the paused time of a
link or of a host is the one of its cells; and there is no wander and no
error of a report. -/
def steadyDraw (y : ∀ p : Component H R, p.Coordinate) : Draw H R where
  split := (canonicalDraw (splitCoordinates y)).split
  offset := fun h => y (.offset h)
  logRate := fun h => y (.logRate h)
  wander := fun _ _ => 0
  linkPaused := fun i j => tamePath (y (.linkPaused i j))
  hostPaused := fun h => tamePath (y (.hostPaused h))
  deviceLogRate := fun x => y (.deviceLogRate x)
  deviceWander := fun _ _ => 0
  reportError := fun _ _ => 0

/-- The draw of every outcome has steady clocks. -/
theorem steadyDraw_steady (y : ∀ p : Component H R, p.Coordinate) : (steadyDraw y).Steady where
  split_mem := canonicalDraw_split_mem (splitCoordinates y)
  no_wander := fun _ _ => rfl
  no_deviceWander := fun _ _ => rfl
  no_reportError := fun _ _ => rfl
  linkPaused_monotone := fun _ _ => tamePath_monotone _
  hostPaused_monotone := fun _ => tamePath_monotone _
  linkPaused_tame := fun _ _ => tamePath_tame _
  hostPaused_tame := fun _ => tamePath_tame _

/-- How each component of the draw of an outcome depends on its coordinate,
when the pairs are taken in the order `o`. -/
def steadyMap (o : Orientation H) : (p : Component H R) → p.Coordinate → p.Val
  | .split z => canonicalMap o (.split z)
  | .offset _ => fun u => u
  | .logRate _ => fun u => u
  | .wander _ => fun _ _ => 0
  | .linkPaused _ _ => tamePath
  | .hostPaused _ => tamePath
  | .deviceLogRate _ => fun u => u
  | .deviceWander _ => fun _ _ => 0
  | .reportError _ => fun _ _ => 0

theorem measurable_steadyMap (o : Orientation H) (p : Component H R) :
    Measurable (steadyMap o p) := by
  cases p with
  | split z => exact measurable_canonicalMap o (.split z)
  | offset h => exact measurable_id
  | logRate h => exact measurable_id
  | wander h => exact measurable_const
  | linkPaused i j => exact measurable_tamePath
  | hostPaused h => exact measurable_tamePath
  | deviceLogRate x => exact measurable_id
  | deviceWander x => exact measurable_const
  | reportError x => exact measurable_const

theorem steadyDraw_component (o : Orientation H) (p : Component H R)
    (y : ∀ p : Component H R, p.Coordinate) :
    (steadyDraw y).component o p = steadyMap o p (y p) := by
  cases p with
  | split z => exact canonicalDraw_component o (.split z) (splitCoordinates y)
  | offset h => rfl
  | logRate h => rfl
  | wander h => rfl
  | linkPaused i j => rfl
  | hostPaused h => rfl
  | deviceLogRate x => rfl
  | deviceWander x => rfl
  | reportError x => rfl

variable [Fintype H]

/-- **The draw of an outcome has the law of a member with steady clocks.** -/
theorem steadyDraw_prior (m : GenerativeWorld H R) (f : Member H R) (hf : f.SteadyClocks) :
    m.Prior f (Measure.pi (steadyLaw m f)) (steadyDraw (H := H)) where
  prob := inferInstance
  split_swap := fun y => canonicalDraw_split_swap (splitCoordinates y)
  split_mem := fun y => canonicalDraw_split_mem (splitCoordinates y)
  split_law := fun i j hij =>
    hasLaw_canonicalDraw_split m.shape hij
      (Y := fun y : ∀ p : Component H R, p.Coordinate => splitCoordinates y)
      (measurePreserving_eval (steadyLaw m f) (.split (pairOf i j hij))).hasLaw
  offset_law := fun h => (measurePreserving_eval (steadyLaw m f) (.offset h)).hasLaw
  logRate_law := fun h => (measurePreserving_eval (steadyLaw m f) (.logRate h)).hasLaw
  wander_gaussian := fun _ => isGaussianProcess_zero _
  wander_mean := fun _ _ => by simp [steadyDraw]
  wander_covariance := fun h _ _ => by
    simp only [steadyDraw]
    rw [covariance_const_left, hf.no_wander h]
    simp
  wander_continuous := fun _ _ => continuous_const
  deviceLogRate_law := fun x =>
    (measurePreserving_eval (steadyLaw m f) (.deviceLogRate x)).hasLaw
  deviceWander_gaussian := fun _ => isGaussianProcess_zero _
  deviceWander_mean := fun _ _ => by simp [steadyDraw]
  deviceWander_covariance := fun x _ _ => by
    simp only [steadyDraw]
    rw [covariance_const_left, hf.no_deviceWander x]
    simp
  deviceWander_continuous := fun _ _ => continuous_const
  reportError_gaussian := fun _ => isGaussianProcess_zero _
  reportError_mean := fun _ _ => by simp [steadyDraw]
  reportError_covariance := fun x _ _ => by
    simp only [steadyDraw]
    rw [covariance_const_left, hf.no_reportError x]
    simp
  reportError_continuous := fun _ _ => continuous_const
  linkPaused_monotone := fun _ _ _ => tamePath_monotone _
  linkPaused_zero := fun _ _ _ => tamePath_zero _
  linkPaused_rightContinuous := fun _ _ _ t => tamePath_rightContinuous _ t
  linkPaused_increments := fun i j =>
    have := f.linkPauseLength_prob i j
    hasIndepIncrements_tamePath (f.linkPauseRate_nonneg i j) (f.linkPauseLength_pos i j)
      (f.linkPauseLength_mean i j) (f.linkLoad_lt_one i j)
      (measurePreserving_eval (steadyLaw m f) (.linkPaused i j))
  linkPaused_law := fun i j s t hst =>
    have := f.linkPauseLength_prob i j
    hasLaw_tamePath_sub (f.linkPauseRate_nonneg i j) (f.linkPauseLength_pos i j)
      (f.linkPauseLength_mean i j) (f.linkLoad_lt_one i j)
      (measurePreserving_eval (steadyLaw m f) (.linkPaused i j)) hst
  hostPaused_monotone := fun _ _ => tamePath_monotone _
  hostPaused_zero := fun _ _ => tamePath_zero _
  hostPaused_rightContinuous := fun _ _ t => tamePath_rightContinuous _ t
  hostPaused_increments := fun h =>
    have := f.hostPauseLength_prob h
    hasIndepIncrements_tamePath (f.hostPauseRate_nonneg h) (f.hostPauseLength_pos h)
      (f.hostPauseLength_mean h) (f.hostLoad_lt_one h)
      (measurePreserving_eval (steadyLaw m f) (.hostPaused h))
  hostPaused_law := fun h s t hst =>
    have := f.hostPauseLength_prob h
    hasLaw_tamePath_sub (f.hostPauseRate_nonneg h) (f.hostPauseLength_pos h)
      (f.hostPauseLength_mean h) (f.hostLoad_lt_one h)
      (measurePreserving_eval (steadyLaw m f) (.hostPaused h)) hst
  independent := fun o => by
    have h : (fun p (y : ∀ p : Component H R, p.Coordinate) => (steadyDraw y).component o p)
        = fun p (y : ∀ p : Component H R, p.Coordinate) => steadyMap o p (y p) := by
      funext p y
      exact steadyDraw_component o p y
    rw [h]
    exact iIndepFun_pi fun p => (measurable_steadyMap o p).aemeasurable

end Draw

/-! ## The random world -/

section World

variable [DecidableEq H]

/-- The world of an outcome: the world of its draw. -/
def steadyWorld (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : ∀ p : Component H R, p.Coordinate) :
    World H R :=
  drawWorld m f hex (steadyDraw y) (steadyDraw_steady y)

/-- The world of every outcome is built from the draw of the outcome. -/
theorem steadyWorld_builds (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : ∀ p : Component H R, p.Coordinate) :
    m.Builds f (steadyDraw y) (steadyWorld m f hex y) :=
  drawWorld_builds m f hex (steadyDraw y) (steadyDraw_steady y)

/-- **Every member with steady clocks has a random world**, with any number
of hosts and speakers. Its links and its hosts may pause, at any rates and
with any laws of the lengths, and the mean rates of its clocks may be spread.
The outcomes are the coordinates of the components, drawn independently, and
the world of an outcome is the world of its draw. -/
theorem exists_holds_of_steadyClocks [Fintype H] (m : GenerativeWorld H R) (f : Member H R)
    (hf : f.SteadyClocks) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (world : Ω → World H R),
      m.Holds f P world :=
  ⟨∀ p : Component H R, p.Coordinate, inferInstance, Measure.pi (steadyLaw m f),
    steadyWorld m f hex, steadyDraw, steadyDraw_prior m f hf,
    fun y => steadyWorld_builds m f hex y⟩

/-- A member in which every link and every host pauses once per second on
average, each time for a hundredth of a second, and in which the logarithms
of the mean rates of the clocks have standard deviation one. Its clocks are
steady. -/
def pausingMember (H : Type) (R : ℕ) : Member H R where
  roundTrip := fun _ _ => 1
  roundTrip_pos := fun _ _ => one_pos
  roundTrip_symm := fun _ _ => rfl
  linkPauseRate := fun _ _ => 1
  linkPauseRate_nonneg := fun _ _ => zero_le_one
  linkPauseLength := fun _ _ => Measure.dirac (1 / 100)
  linkPauseLength_prob := fun _ _ => inferInstance
  linkPauseLength_pos := fun _ _ => by
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    simp
  linkPauseLength_mean := fun _ _ => integrable_dirac eNorm_lt_top
  linkLoad_lt_one := fun _ _ => by
    rw [integral_dirac]
    norm_num
  hostPauseRate := fun _ => 1
  hostPauseRate_nonneg := fun _ => zero_le_one
  hostPauseLength := fun _ => Measure.dirac (1 / 100)
  hostPauseLength_prob := fun _ => inferInstance
  hostPauseLength_pos := fun _ => by
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    simp
  hostPauseLength_mean := fun _ => integrable_dirac eNorm_lt_top
  hostLoad_lt_one := fun _ => by
    rw [integral_dirac]
    norm_num
  rateSpread := 1
  rateSpread_nonneg := zero_le_one
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
  speakerStart := fun _ => 0

/-- **The generative model has members whose links and hosts pause, with a
random world**, for any hosts and speakers. In the member of this example
every link and every host pauses, and the mean rates of the clocks are
spread. -/
theorem exists_holds_with_pauses [Fintype H] (m : GenerativeWorld H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    ∃ (f : Member H R) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (world : Ω → World H R),
      m.Holds f P world ∧ (∀ i j, 0 < f.linkPauseRate i j) ∧ (∀ h, 0 < f.hostPauseRate h)
        ∧ 0 < f.rateSpread := by
  obtain ⟨Ω, mΩ, P, world, hworld⟩ := exists_holds_of_steadyClocks m (pausingMember H R)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ hex
  exact ⟨pausingMember H R, Ω, mΩ, P, world, hworld, fun _ _ => one_pos, fun _ => one_pos,
    one_pos⟩

end World

end Unisono.Spec.GenerativeWorld
