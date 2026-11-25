/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeDelivery
public import Unisono.Spec.Models.Ideal
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Generative worlds without noise are ideal constant worlds

A member of the generative model is *noiseless* when its links and its hosts
never pause, the clocks of its hosts and of its audio devices do not wander,
the mean rates of those clocks have no spread, and its audio devices report
exact timestamps (`Member.Noiseless`). What remains random in such a member is
what no host can learn: the offset of each clock and the split of each pair
of hosts.

In a noiseless member, almost every drawn world is an ideal constant world
(`Prior.ae_idealConstantWorld`): every clock runs at the rate of true time
with its drawn offset, every device runs at the nominal rate, and every
message from `i` to `j` takes the constant delay `split i j * roundTrip i j`.
The theorems about ideal constant worlds and about bounded worlds therefore
hold in almost every outcome of a noiseless member.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-- A world has finitely many hosts: the sender's host and the hosts of the
speakers. -/
theorem World.finite_hosts (w : World H R) : Finite H := by
  let g : Option (Fin R) → H := fun o => o.elim w.sender w.host
  refine Finite.of_surjective g fun h => ?_
  rcases w.hosts h with hs | ⟨r, hr⟩
  · exact ⟨none, hs.symm⟩
  · exact ⟨some r, hr⟩

namespace GenerativeWorld

variable {Ω : Type} [MeasurableSpace Ω]
variable {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}

/-- A member is noiseless: its links and its hosts never pause, the clocks of
its hosts and of its audio devices do not wander, the mean rates of those
clocks have no spread, and its audio devices report exact timestamps. -/
structure Member.Noiseless (f : Member H R) : Prop where
  no_linkPauses : ∀ i j, f.linkPauseRate i j = 0
  no_hostPauses : ∀ h, f.hostPauseRate h = 0
  no_wander : ∀ h, f.wanderSize h = 0
  no_deviceWander : ∀ x, f.deviceWanderSize x = 0
  no_reportError : ∀ x, f.reportSize x = 0
  no_spread : f.rateSpread = 0

/-- With no spread of the mean rates, the mean rate of every clock is one in
almost every outcome. -/
theorem Prior.logRate_ae_eq_zero (hD : m.Prior f P D) (hf : f.rateSpread = 0) (h : H) :
    ∀ᵐ ω ∂P, (D ω).logRate h = 0 := by
  have hlaw := hD.logRate_law h
  have h0 : Real.toNNReal (f.rateSpread ^ 2) = 0 := by simp [hf]
  rw [h0, gaussianReal_zero_var] at hlaw
  exact hlaw.ae_eq_of_dirac

/-- With no spread of the mean rates, the mean rate of the clock of every
audio device is one in almost every outcome. -/
theorem Prior.deviceLogRate_ae_eq_zero (hD : m.Prior f P D) (hf : f.rateSpread = 0)
    (x : Option (Fin R)) : ∀ᵐ ω ∂P, (D ω).deviceLogRate x = 0 := by
  have hlaw := hD.deviceLogRate_law x
  have h0 : Real.toNNReal (f.rateSpread ^ 2) = 0 := by simp [hf]
  rw [h0, gaussianReal_zero_var] at hlaw
  exact hlaw.ae_eq_of_dirac

/-- A Gaussian process with mean zero whose variance is zero at every time,
and whose paths are continuous, is zero at all times in almost every
outcome. -/
private theorem ae_eq_zero_of_gaussian [IsProbabilityMeasure P] {X : Ω → Time → ℝ}
    (hg : IsGaussianProcess (fun t ω => X ω t) P) (hmean : ∀ t, ∫ ω, X ω t ∂P = 0)
    (hcov : ∀ t, cov[fun ω => X ω t, fun ω => X ω t; P] = 0)
    (hcont : ∀ ω, Continuous (X ω)) : ∀ᵐ ω ∂P, ∀ t, X ω t = 0 := by
  have hpoint : ∀ t : ℝ, ∀ᵐ ω ∂P, X ω t = 0 := by
    intro t
    have hgt : HasGaussianLaw (fun ω => X ω t) P := hg.hasGaussianLaw_eval t
    have hmap := hgt.map_eq_gaussianReal
    have hm : P[fun ω => X ω t] = 0 := hmean t
    have hvar : Var[fun ω => X ω t; P] = 0 := by
      rw [← covariance_self hgt.aemeasurable, hcov t]
    rw [hm, hvar, Real.toNNReal_zero, gaussianReal_zero_var] at hmap
    exact (HasLaw.mk hgt.aemeasurable hmap).ae_eq_of_dirac
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, X ω (q : ℝ) = 0 :=
    ae_all_iff.mpr fun q => hpoint q
  filter_upwards [hrat] with ω hω
  have heq : X ω = fun _ => (0 : ℝ) :=
    Continuous.ext_on (Rat.denseRange_cast (𝕜 := ℝ)) (hcont ω)
      continuous_const (by rintro _ ⟨q, rfl⟩; exact hω q)
  intro t
  exact congrFun heq t

/-- A clock whose wander has size zero does not wander, in almost every
outcome. -/
theorem Prior.wander_ae_eq_zero (hD : m.Prior f P D) {h : H} (hf : f.wanderSize h = 0) :
    ∀ᵐ ω ∂P, ∀ t, (D ω).wander h t = 0 := by
  have := hD.prob
  refine ae_eq_zero_of_gaussian (hD.wander_gaussian h) (hD.wander_mean h) (fun t => ?_)
    (fun ω => hD.wander_continuous ω h)
  rw [hD.wander_covariance h t t, hf]
  simp

/-- The clock of an audio device whose wander has size zero does not wander,
in almost every outcome. -/
theorem Prior.deviceWander_ae_eq_zero (hD : m.Prior f P D) {x : Option (Fin R)}
    (hf : f.deviceWanderSize x = 0) : ∀ᵐ ω ∂P, ∀ t, (D ω).deviceWander x t = 0 := by
  have := hD.prob
  refine ae_eq_zero_of_gaussian (hD.deviceWander_gaussian x) (hD.deviceWander_mean x)
    (fun t => ?_) (fun ω => hD.deviceWander_continuous ω x)
  rw [hD.deviceWander_covariance x t t, hf]
  simp

/-- An audio device whose reports have an error of size zero reports exact
timestamps, in almost every outcome. -/
theorem Prior.reportError_ae_eq_zero (hD : m.Prior f P D) {x : Option (Fin R)}
    (hf : f.reportSize x = 0) : ∀ᵐ ω ∂P, ∀ t, (D ω).reportError x t = 0 := by
  have := hD.prob
  refine ae_eq_zero_of_gaussian (hD.reportError_gaussian x) (hD.reportError_mean x)
    (fun t => ?_) (fun ω => hD.reportError_continuous ω x)
  rw [hD.reportError_covariance x t t, hf]
  simp

/-- A quantity that never decreases in time, and that is the same at any two
given times in almost every outcome, is the same at all times in almost
every outcome. -/
private theorem ae_const_of_monotone {X : Ω → Time → ℝ} (hmono : ∀ ω, Monotone (X ω))
    (hpoint : ∀ s t : ℝ, s ≤ t → ∀ᵐ ω ∂P, X ω t - X ω s = 0) :
    ∀ᵐ ω ∂P, ∀ s t, X ω s = X ω t := by
  have hrat : ∀ᵐ ω ∂P, ∀ p q : ℚ, (p : ℝ) ≤ q → X ω q - X ω p = 0 := by
    rw [ae_all_iff]
    intro p
    rw [ae_all_iff]
    intro q
    by_cases hpq : (p : ℝ) ≤ q
    · filter_upwards [hpoint p q hpq] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hpq
  filter_upwards [hrat] with ω hω
  have hle : ∀ s t : ℝ, X ω t ≤ X ω s := by
    intro s t
    obtain ⟨p, hp⟩ := exists_rat_lt (min s t)
    obtain ⟨q, hq⟩ := exists_rat_gt (max s t)
    have hps : (p : ℝ) ≤ s := hp.le.trans (min_le_left s t)
    have htq : t ≤ (q : ℝ) := (le_max_right s t).trans hq.le
    have hsq : s ≤ (q : ℝ) := (le_max_left s t).trans hq.le
    have h0 := hω p q (hps.trans hsq)
    have h1 := hmono ω hps
    have h2 := hmono ω htq
    linarith
  intro s t
  exact le_antisymm (hle t s) (hle s t)

/-- A link that never pauses has no paused time, in almost every outcome:
the paused time that has begun is the same at all times. -/
theorem Prior.linkPaused_ae_const (hD : m.Prior f P D) {i j : H}
    (hf : f.linkPauseRate i j = 0) :
    ∀ᵐ ω ∂P, ∀ s t, (D ω).linkPaused i j s = (D ω).linkPaused i j t := by
  refine ae_const_of_monotone (fun ω => hD.linkPaused_monotone ω i j) fun s t hst => ?_
  have hlaw := hD.linkPaused_law i j s t hst
  rw [hf, zero_mul, Real.toNNReal_zero, pauseLaw_zero] at hlaw
  exact hlaw.ae_eq_of_dirac

/-- A host that never pauses has no paused time, in almost every outcome:
the paused time that has begun is the same at all times. -/
theorem Prior.hostPaused_ae_const (hD : m.Prior f P D) {h : H}
    (hf : f.hostPauseRate h = 0) :
    ∀ᵐ ω ∂P, ∀ s t, (D ω).hostPaused h s = (D ω).hostPaused h t := by
  refine ae_const_of_monotone (fun ω => hD.hostPaused_monotone ω h) fun s t hst => ?_
  have hlaw := hD.hostPaused_law h s t hst
  rw [hf, zero_mul, Real.toNNReal_zero, pauseLaw_zero] at hlaw
  exact hlaw.ae_eq_of_dirac

/-- A clock with mean rate one that does not wander reads true time plus its
offset. -/
theorem Draw.reading_of_noiseless {d : Draw H R} {h : H} (h0 : d.logRate h = 0)
    (hw : ∀ t, d.wander h t = 0) (t : Time) : d.reading h t = d.offset h + t := by
  simp [Draw.reading, h0, hw]

/-- The clock of an audio device with mean rate one that does not wander
advances with true time. -/
theorem Draw.deviceReading_noiseless {d : Draw H R} {x : Option (Fin R)}
    (h0 : d.deviceLogRate x = 0) (hw : ∀ t, d.deviceWander x t = 0) (t : Time) :
    d.deviceReading x t = t := by
  simp [Draw.deviceReading, h0, hw]

/-- The ideal constant world model of an outcome of a draw: the settings of
the generative model, with the least delays of the outcome as its constant
delays. -/
def Prior.idealWorld (hD : m.Prior f P D) (ω : Ω) : IdealConstantWorld H R where
  rate := m.rate
  rate_pos := m.rate_pos
  sender := m.sender
  host := m.host
  delay := fun i j => (D ω).split i j * f.roundTrip i j
  delay_pos := fun i j => hD.leastDelay_pos ω i j
  blockSize := m.blockSize
  blockSize_pos := m.blockSize_pos
  lead := m.lead
  lead_pos := m.lead_pos
  targetLatency := m.targetLatency
  targetLatency_nonneg := m.targetLatency_nonneg

/-- **A noiseless member draws ideal constant worlds.** In a noiseless member
of the generative model, almost every outcome is an ideal constant world:
every message from `i` to `j` takes the constant delay
`split i j * roundTrip i j`, every device runs at the nominal rate, and the
clock of each host reads true time plus the host's drawn offset. -/
theorem Prior.ae_idealConstantWorld (hD : m.Prior f P D) (hf : f.Noiseless)
    {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω)) :
    ∀ᵐ ω ∂P, (hD.idealWorld ω).Holds (world ω)
      ∧ ∀ h t, ((world ω).clock h).read t = t + (D ω).offset h := by
  have := hD.prob
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have : Finite H := (world ω₀).finite_hosts
  have h1 : ∀ᵐ ω ∂P, ∀ h, (D ω).logRate h = 0 :=
    ae_all_iff.mpr fun h => hD.logRate_ae_eq_zero hf.no_spread h
  have h2 : ∀ᵐ ω ∂P, ∀ h t, (D ω).wander h t = 0 :=
    ae_all_iff.mpr fun h => hD.wander_ae_eq_zero (hf.no_wander h)
  have h3 : ∀ᵐ ω ∂P, ∀ i j s t, (D ω).linkPaused i j s = (D ω).linkPaused i j t :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      hD.linkPaused_ae_const (hf.no_linkPauses i j)
  have h4 : ∀ᵐ ω ∂P, ∀ h s t, (D ω).hostPaused h s = (D ω).hostPaused h t :=
    ae_all_iff.mpr fun h => hD.hostPaused_ae_const (hf.no_hostPauses h)
  have h5 : ∀ᵐ ω ∂P, ∀ x, (D ω).deviceLogRate x = 0 :=
    ae_all_iff.mpr fun x => hD.deviceLogRate_ae_eq_zero hf.no_spread x
  have h6 : ∀ᵐ ω ∂P, ∀ x t, (D ω).deviceWander x t = 0 :=
    ae_all_iff.mpr fun x => hD.deviceWander_ae_eq_zero (hf.no_deviceWander x)
  have h7 : ∀ᵐ ω ∂P, ∀ x t, (D ω).reportError x t = 0 :=
    ae_all_iff.mpr fun x => hD.reportError_ae_eq_zero (hf.no_reportError x)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7] with ω hr hw ht hh hdr hdw herr
  have hdev : ∀ x t, (D ω).deviceReading x t = t := fun x t =>
    Draw.deviceReading_noiseless (hdr x) (hdw x) t
  have hclock : ∀ h t, ((world ω).clock h).read t = t + (D ω).offset h := by
    intro h t
    rw [(hB ω).clock h t, Draw.reading_of_noiseless (hr h) (hw h) t, add_comm]
  refine ⟨?_, hclock⟩
  exact
    { rate_eq := (hB ω).rate_eq
      sender_eq := (hB ω).sender_eq
      host_eq := (hB ω).host_eq
      clocks := fun h => ⟨(D ω).offset h, hclock h⟩
      capture := ⟨f.captureStart - (D ω).offset (world ω).sender, fun n => by
        have h := (hB ω).capture n
        have h0 := (hB ω).capture_start
        rw [hclock] at h0
        rw [hdev, hdev] at h
        simp only [Prior.idealWorld]
        linarith⟩
      capture_first := (hB ω).capture_first
      capture_handed := (hB ω).handed_of_const (hh _)
      capture_reported := fun b => by
        rw [(hB ω).capture_reported b, herr, add_zero]
        simp
      speaker_out := fun r =>
        ⟨f.speakerStart (m.device r) - (D ω).offset ((world ω).host r), fun k => by
          have h := (hB ω).speaker_out r k
          have h0 := (hB ω).speaker_start r
          rw [hclock] at h0
          rw [hdev, hdev] at h
          simp only [Prior.idealWorld]
          linarith⟩
      speaker_first := (hB ω).speaker_first
      speaker_asked := fun r b => by
        have h := (hB ω).asked_of_const (r := r) (hh _) b
        rw [hdev, hdev] at h
        simp only [Prior.idealWorld]
        linarith
      speaker_reported := fun r b => by
        rw [(hB ω).speaker_reported r b, herr, add_zero]
        simp
      network := fun i j s q => by
        obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hdel⟩ := (hB ω).network i j s q
        have h₁ : v₁ = 0 := hv₁.unique (isBacklog_zero_of_const (hh i) s)
        have h₂ : v₂ = 0 := hv₂.unique (isBacklog_zero_of_const (ht i j) _)
        have h₃ : v₃ = 0 := hv₃.unique (isBacklog_zero_of_const (hh j) _)
        rw [hdel, h₁, h₂, h₃]
        simp only [add_zero]
        rfl
      target_eq := (hB ω).target_eq }

/-- In a noiseless member, almost every outcome satisfies the tight bounds of
its ideal constant world, so the theorems about bounded worlds apply to it. -/
theorem Prior.ae_withinBounds (hD : m.Prior f P D) (hf : f.Noiseless)
    {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω)) :
    ∀ᵐ ω ∂P, (world ω).WithinBounds (hD.idealWorld ω).toBounds := by
  filter_upwards [hD.ae_idealConstantWorld hf hB] with ω hω
  exact IdealConstantWorld.withinBounds hω.1

end GenerativeWorld

end Unisono.Spec
