/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeWorld
public import Unisono.Spec.Models.Ideal
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Generative worlds without noise are ideal constant worlds

A member of the generative model is *noiseless* when its links carry no
other traffic, its clocks do not wander, and the mean rates of its clocks
have no spread (`Member.Noiseless`). What remains random in such a member is
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
variable {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H}

/-- A member is noiseless: its links carry no other traffic, its clocks do
not wander, and the mean rates of its clocks have no spread. -/
structure Member.Noiseless (f : Member H R) : Prop where
  no_traffic : ∀ i j, f.trafficRate i j = 0
  no_wander : ∀ h, f.wanderSize h = 0
  no_spread : f.rateSpread = 0

/-- With no spread of the mean rates, the mean rate of every clock is one in
almost every outcome. -/
theorem Prior.logRate_ae_eq_zero (hD : m.Prior f P D) (hf : f.rateSpread = 0) (h : H) :
    ∀ᵐ ω ∂P, (D ω).logRate h = 0 := by
  have hlaw := hD.logRate_law h
  have h0 : Real.toNNReal (f.rateSpread ^ 2) = 0 := by simp [hf]
  rw [h0, gaussianReal_zero_var] at hlaw
  exact hlaw.ae_eq_of_dirac

/-- A clock whose wander has size zero does not wander, in almost every
outcome. -/
theorem Prior.wander_ae_eq_zero (hD : m.Prior f P D) {h : H} (hf : f.wanderSize h = 0) :
    ∀ᵐ ω ∂P, ∀ t, (D ω).wander h t = 0 := by
  have := hD.prob
  have hpoint : ∀ t : ℝ, ∀ᵐ ω ∂P, (D ω).wander h t = 0 := by
    intro t
    have hg : HasGaussianLaw (fun ω => (D ω).wander h t) P :=
      (hD.wander_gaussian h).hasGaussianLaw_eval t
    have hmap := hg.map_eq_gaussianReal
    have hmean : P[fun ω => (D ω).wander h t] = 0 := hD.wander_mean h t
    have hvar : Var[fun ω => (D ω).wander h t; P] = 0 := by
      rw [← covariance_self hg.aemeasurable, hD.wander_covariance h t t, hf]
      simp
    rw [hmean, hvar, Real.toNNReal_zero, gaussianReal_zero_var] at hmap
    exact (HasLaw.mk hg.aemeasurable hmap).ae_eq_of_dirac
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, (D ω).wander h (q : ℝ) = 0 :=
    ae_all_iff.mpr fun q => hpoint q
  filter_upwards [hrat] with ω hω
  have heq : (D ω).wander h = fun _ => (0 : ℝ) :=
    Continuous.ext_on (Rat.denseRange_cast (𝕜 := ℝ)) (hD.wander_continuous ω h)
      continuous_const (by rintro _ ⟨q, rfl⟩; exact hω q)
  intro t
  exact congrFun heq t

/-- A link with no other traffic receives no work, in almost every outcome:
the work that has arrived is the same at all times. -/
theorem Prior.traffic_ae_const (hD : m.Prior f P D) {i j : H} (hf : f.trafficRate i j = 0) :
    ∀ᵐ ω ∂P, ∀ s t, (D ω).traffic i j s = (D ω).traffic i j t := by
  have hpoint : ∀ s t : ℝ, s ≤ t →
      ∀ᵐ ω ∂P, (D ω).traffic i j t - (D ω).traffic i j s = 0 := by
    intro s t hst
    have hlaw := hD.traffic_law i j s t hst
    rw [hf, zero_mul, Real.toNNReal_zero, trafficLaw_zero] at hlaw
    exact hlaw.ae_eq_of_dirac
  have hrat : ∀ᵐ ω ∂P, ∀ p q : ℚ, (p : ℝ) ≤ q →
      (D ω).traffic i j q - (D ω).traffic i j p = 0 := by
    rw [ae_all_iff]
    intro p
    rw [ae_all_iff]
    intro q
    by_cases hpq : (p : ℝ) ≤ q
    · filter_upwards [hpoint p q hpq] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hpq
  filter_upwards [hrat] with ω hω
  have hmono := hD.traffic_monotone ω i j
  have hle : ∀ s t : ℝ, (D ω).traffic i j t ≤ (D ω).traffic i j s := by
    intro s t
    obtain ⟨p, hp⟩ := exists_rat_lt (min s t)
    obtain ⟨q, hq⟩ := exists_rat_gt (max s t)
    have hps : (p : ℝ) ≤ s := hp.le.trans (min_le_left s t)
    have htq : t ≤ (q : ℝ) := (le_max_right s t).trans hq.le
    have hsq : s ≤ (q : ℝ) := (le_max_left s t).trans hq.le
    have h0 := hω p q (hps.trans hsq)
    have h1 := hmono hps
    have h2 := hmono htq
    linarith
  intro s t
  exact le_antisymm (hle t s) (hle s t)

/-- When no work arrives on a link, its backlog is zero. -/
theorem Draw.isBacklog_zero_of_const {d : Draw H} {i j : H}
    (hc : ∀ s t, d.traffic i j s = d.traffic i j t) (t : Time) : d.IsBacklog i j t 0 := by
  constructor
  · rintro x ⟨s, hs, rfl⟩
    rw [hc t s]
    linarith
  · intro u hu
    exact hu ⟨t, le_rfl, by simp⟩

/-- A clock with mean rate one that does not wander reads true time plus its
offset. -/
theorem Draw.reading_of_noiseless {d : Draw H} {h : H} (h0 : d.logRate h = 0)
    (hw : ∀ t, d.wander h t = 0) (t : Time) : d.reading h t = d.offset h + t := by
  simp [Draw.reading, h0, hw]

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
  have h3 : ∀ᵐ ω ∂P, ∀ i j s t, (D ω).traffic i j s = (D ω).traffic i j t :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hD.traffic_ae_const (hf.no_traffic i j)
  filter_upwards [h1, h2, h3] with ω hr hw ht
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
        rw [hclock] at h
        simp only [Prior.idealWorld]
        linarith⟩
      capture_first := (hB ω).capture_first
      capture_handed := (hB ω).capture_handed
      capture_reported := fun b => by
        rw [(hB ω).capture_reported b]
        simp
      speaker_out := fun r => ⟨f.speakerStart r - (D ω).offset ((world ω).host r), fun k => by
        have h := (hB ω).speaker_out r k
        rw [hclock] at h
        simp only [Prior.idealWorld]
        linarith⟩
      speaker_first := (hB ω).speaker_first
      speaker_asked := fun r b => by
        have h := (hB ω).speaker_asked r b
        rw [hclock, hclock] at h
        simp only [Prior.idealWorld]
        linarith
      speaker_reported := fun r b => by
        rw [(hB ω).speaker_reported r b]
        simp
      network := fun i j s q => by
        obtain ⟨v, hv, hdel⟩ := (hB ω).network i j s q
        have hv0 : v = 0 := hv.unique (Draw.isBacklog_zero_of_const (ht i j) s)
        rw [hdel, hv0, add_zero]
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
