/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedBuild
public import Unisono.Spec.Models.StationaryGaussian

/-!
# Every member of the proposed model has a random world

`exists_holds`: for every member of `Unisono.Spec.ProposedWorld`, with
finitely many hosts, there are a probability space and a random world on it
that belongs to the member (`Holds`). The clocks wander, the links have
jitter, outages, single losses and pauses, and the hosts pause, as the
member says.

The probability space is a product: one coordinate for each part of a draw
(`Part.Coordinate`), with the law of the part (`partLaw`), all independent.

* The split of a pair, the offset and the logarithm of the mean rate of a
  clock are numbers.
* Each part of the wander of a clock, and the error of the reports of an
  audio device, is the path of a stationary Gaussian process with continuous
  paths (`stationaryPath`).
* The count of the jitter of a link is the path of a Poisson process
  (`pausedPath` with episodes of length one); its levels are a sequence of
  independent values with the link's law.
* The paused time of a link or of a host and the outage time of a link are
  paths of episodes that begin at the instants of a Poisson process and leave
  a finite backlog (`tamePath`).
* Whether a link drops a message on its own is one value for each message.

Almost every outcome gives a regular draw (`ae_regular`): what holds only
almost surely is that every clock advances without bound. The outcomes whose
draw is not regular are given the draw of one fixed regular outcome
(`Prior.comp_ae_eq` keeps the law).
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open GenerativeWorld (Cells cellsLaw pausedPath tamePath Orientation pairOf)

variable {H : Type} {R : ℕ}

/-! ## A draw changed on outcomes of probability zero -/

section Congr

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m : Told H R} {f : Member H R}

/-- Episodes read from outcomes that are changed on a set of probability
zero are episodes with the same rate and law. -/
theorem IsEpisodePath.comp_ae_eq {rate : ℝ} {F : Measure ℝ} {X : Time → Ω → ℝ}
    (hX : IsEpisodePath rate F X P) {φ : Ω → Ω} (hφ : ∀ᵐ ω ∂P, φ ω = ω) :
    IsEpisodePath rate F (fun t ω => X t (φ ω)) P where
  zero := fun ω => hX.zero (φ ω)
  monotone := fun ω => hX.monotone (φ ω)
  rightContinuous := fun ω t => hX.rightContinuous (φ ω) t
  increments := by
    intro n t ht
    refine (hX.increments n t ht).congr fun i => ?_
    filter_upwards [hφ] with ω hω
    simp only [hω]
  law := fun s t hst => (hX.law s t hst).congr (by
    filter_upwards [hφ] with ω hω
    simp only [hω])

/-- **A draw that is changed on a set of outcomes of probability zero has the
same law.** -/
theorem Prior.comp_ae_eq {D : Ω → Draw H R} (hD : Prior m f P D) {φ : Ω → Ω}
    (hφ : ∀ᵐ ω ∂P, φ ω = ω) : Prior m f P fun ω => D (φ ω) where
  prob := hD.prob
  split_swap := fun ω => hD.split_swap (φ ω)
  split_mem := fun ω => hD.split_mem (φ ω)
  split_law := fun i j hij => (hD.split_law i j hij).congr (by
    filter_upwards [hφ] with ω hω
    simp only [hω])
  offset_law := fun h => HasLaw.congr (hD.offset_law h) (by
    filter_upwards [hφ] with ω hω
    simp only [hω])
  logRate_law := fun h => (hD.logRate_law h).congr (by
    filter_upwards [hφ] with ω hω
    simp only [hω])
  wander_gaussian := fun h k => (hD.wander_gaussian h k).congr fun t => by
    filter_upwards [hφ] with ω hω
    simp only [hω]
  wander_mean := fun h k t => by
    rw [← hD.wander_mean h k t]
    exact integral_congr_ae (by
      filter_upwards [hφ] with ω hω
      simp only [hω])
  wander_covariance := fun h k s t => by
    rw [← hD.wander_covariance h k s t]
    exact covariance_congr_ae
      (by filter_upwards [hφ] with ω hω; simp only [hω])
      (by filter_upwards [hφ] with ω hω; simp only [hω])
  wander_continuous := fun ω => hD.wander_continuous (φ ω)
  deviceLogRate_law := fun x => (hD.deviceLogRate_law x).congr (by
    filter_upwards [hφ] with ω hω
    simp only [hω])
  deviceWander_gaussian := fun x k => (hD.deviceWander_gaussian x k).congr fun t => by
    filter_upwards [hφ] with ω hω
    simp only [hω]
  deviceWander_mean := fun x k t => by
    rw [← hD.deviceWander_mean x k t]
    exact integral_congr_ae (by
      filter_upwards [hφ] with ω hω
      simp only [hω])
  deviceWander_covariance := fun x k s t => by
    rw [← hD.deviceWander_covariance x k s t]
    exact covariance_congr_ae
      (by filter_upwards [hφ] with ω hω; simp only [hω])
      (by filter_upwards [hφ] with ω hω; simp only [hω])
  deviceWander_continuous := fun ω => hD.deviceWander_continuous (φ ω)
  reportError_gaussian := fun x => (hD.reportError_gaussian x).congr fun t => by
    filter_upwards [hφ] with ω hω
    simp only [hω]
  reportError_mean := fun x t => by
    rw [← hD.reportError_mean x t]
    exact integral_congr_ae (by
      filter_upwards [hφ] with ω hω
      simp only [hω])
  reportError_covariance := fun x s t => by
    rw [← hD.reportError_covariance x s t]
    exact covariance_congr_ae
      (by filter_upwards [hφ] with ω hω; simp only [hω])
      (by filter_upwards [hφ] with ω hω; simp only [hω])
  reportError_continuous := fun ω => hD.reportError_continuous (φ ω)
  jitterCount_law := fun i j => (hD.jitterCount_law i j).comp_ae_eq hφ
  jitterLevel_law := fun i j => (hD.jitterLevel_law i j).congr (by
    filter_upwards [hφ] with ω hω
    simp only [hω])
  jitterLevel_nonneg := fun ω => hD.jitterLevel_nonneg (φ ω)
  linkPaused_law := fun i j => (hD.linkPaused_law i j).comp_ae_eq hφ
  outage_law := fun i j => (hD.outage_law i j).comp_ae_eq hφ
  dropped_law := fun i j q => (hD.dropped_law i j q).congr (by
    filter_upwards [hφ] with ω hω
    simp only [hω])
  hostPaused_law := fun h => (hD.hostPaused_law h).comp_ae_eq hφ
  independent := fun o => (hD.independent o).congr fun p => by
    filter_upwards [hφ] with ω hω
    simp only [hω]

end Congr

/-! ## The probability space -/

/-- The coordinate of an outcome that belongs to each part of a draw. -/
def Part.Coordinate : Part H R → Type
  | .split _ => ℝ
  | .offset _ => ℝ
  | .logRate _ => ℝ
  | .wander _ _ => ℝ≥0 → ℝ
  | .deviceLogRate _ => ℝ
  | .deviceWander _ _ => ℝ≥0 → ℝ
  | .reportError _ => ℝ≥0 → ℝ
  | .jitterCount _ _ => Cells
  | .jitterLevel _ _ => ℤ → ℝ
  | .linkPaused _ _ => Cells
  | .outage _ _ => Cells
  | .dropped _ _ _ => Bool
  | .hostPaused _ => Cells

instance (p : Part H R) : MeasurableSpace p.Coordinate := by
  cases p
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace (ℝ≥0 → ℝ))
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace (ℝ≥0 → ℝ))
  · exact inferInstanceAs (MeasurableSpace (ℝ≥0 → ℝ))
  · exact inferInstanceAs (MeasurableSpace Cells)
  · exact inferInstanceAs (MeasurableSpace (ℤ → ℝ))
  · exact inferInstanceAs (MeasurableSpace Cells)
  · exact inferInstanceAs (MeasurableSpace Cells)
  · exact inferInstanceAs (MeasurableSpace Bool)
  · exact inferInstanceAs (MeasurableSpace Cells)

/-- The law of each coordinate. -/
def partLaw (m : Told H R) (f : Member H R) : (p : Part H R) → Measure p.Coordinate
  | .split _ => (betaMeasure m.shape m.shape : Measure ℝ)
  | .offset _ =>
    (ProbabilityTheory.cond volume (Set.Icc (-f.offsetRange) f.offsetRange) : Measure ℝ)
  | .logRate _ => gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))
  | .wander h k => stationaryLaw (f.wanderSize h k) (f.wanderTime h k)
  | .deviceLogRate _ => gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))
  | .deviceWander x k => stationaryLaw (f.deviceWanderSize x k) (f.deviceWanderTime x k)
  | .reportError x => stationaryLaw (f.reportSize x) (f.reportTime x)
  | .jitterCount i j => cellsLaw (Real.toNNReal (f.jitterRate i j)) (Measure.dirac 1)
  | .jitterLevel i j => Measure.infinitePi fun _ : ℤ => f.jitterLaw i j
  | .linkPaused i j => cellsLaw (Real.toNNReal (f.linkPauseRate i j)) (f.linkPauseLength i j)
  | .outage i j => cellsLaw (Real.toNNReal (f.outageRate i j)) (f.outageLength i j)
  | .dropped i j _ => dropLaw (f.lossProbability i j)
  | .hostPaused h => cellsLaw (Real.toNNReal (f.hostPauseRate h)) (f.hostPauseLength h)

instance (m : Told H R) (f : Member H R) (p : Part H R) :
    IsProbabilityMeasure (partLaw m f p) := by
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
  | wander h k => exact inferInstanceAs (IsProbabilityMeasure (stationaryLaw _ _))
  | deviceLogRate x => exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 _))
  | deviceWander x k => exact inferInstanceAs (IsProbabilityMeasure (stationaryLaw _ _))
  | reportError x => exact inferInstanceAs (IsProbabilityMeasure (stationaryLaw _ _))
  | jitterCount i j =>
    exact inferInstanceAs (IsProbabilityMeasure (cellsLaw _ (Measure.dirac (1 : ℝ))))
  | jitterLevel i j =>
    exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℤ => f.jitterLaw i j))
  | linkPaused i j =>
    have := f.linkPauseLength_prob i j
    exact inferInstanceAs (IsProbabilityMeasure (cellsLaw _ (f.linkPauseLength i j)))
  | outage i j =>
    have := f.outageLength_prob i j
    exact inferInstanceAs (IsProbabilityMeasure (cellsLaw _ (f.outageLength i j)))
  | dropped i j q =>
    exact dropLaw_prob (f.lossProbability_nonneg i j) (f.lossProbability_lt_one i j).le
  | hostPaused h =>
    have := f.hostPauseLength_prob h
    exact inferInstanceAs (IsProbabilityMeasure (cellsLaw _ (f.hostPauseLength h)))

section Draw

variable [DecidableEq H]

/-- The numbers of an outcome that are drawn for the pairs of hosts, as the
coordinates of the pairs in `GenerativeWorld`. -/
def splitCoordinates (y : ∀ p : Part H R, p.Coordinate) : GenerativeWorld.Component H R → ℝ
  | .split z => y (.split z)
  | _ => 0

/-- **The draw of an outcome.** -/
def canonicalDraw (f : Member H R) (y : ∀ p : Part H R, p.Coordinate) : Draw H R where
  split := (GenerativeWorld.canonicalDraw (splitCoordinates y)).split
  offset := fun h => y (.offset h)
  logRate := fun h => y (.logRate h)
  wander := fun h k => stationaryPath (f.wanderSize h k) (f.wanderTime h k) (y (.wander h k))
  deviceLogRate := fun x => y (.deviceLogRate x)
  deviceWander := fun x k =>
    stationaryPath (f.deviceWanderSize x k) (f.deviceWanderTime x k) (y (.deviceWander x k))
  reportError := fun x => stationaryPath (f.reportSize x) (f.reportTime x) (y (.reportError x))
  jitterCount := fun i j => pausedPath (y (.jitterCount i j))
  jitterLevel := fun i j n => max (y (.jitterLevel i j) n) 0
  linkPaused := fun i j => tamePath (y (.linkPaused i j))
  outage := fun i j => tamePath (y (.outage i j))
  dropped := fun i j q => y (.dropped i j q)
  hostPaused := fun h => tamePath (y (.hostPaused h))

/-- How each part of the draw of an outcome depends on its coordinate, when
the pairs are taken in the order `o`. -/
def partMap (f : Member H R) (o : Orientation H) : (p : Part H R) → p.Coordinate → p.Val
  | .split z => GenerativeWorld.canonicalMap (R := R) o (.split z)
  | .offset _ => fun u => u
  | .logRate _ => fun u => u
  | .wander h k => stationaryPath (f.wanderSize h k) (f.wanderTime h k)
  | .deviceLogRate _ => fun u => u
  | .deviceWander x k => stationaryPath (f.deviceWanderSize x k) (f.deviceWanderTime x k)
  | .reportError x => stationaryPath (f.reportSize x) (f.reportTime x)
  | .jitterCount _ _ => pausedPath
  | .jitterLevel _ _ => fun u n => max (u n) 0
  | .linkPaused _ _ => tamePath
  | .outage _ _ => tamePath
  | .dropped _ _ _ => fun b => b
  | .hostPaused _ => tamePath

theorem measurable_partMap (f : Member H R) (o : Orientation H) (p : Part H R) :
    Measurable (partMap f o p) := by
  cases p with
  | split z => exact GenerativeWorld.measurable_canonicalMap o (.split z)
  | offset h => exact measurable_id
  | logRate h => exact measurable_id
  | wander h k => exact measurable_stationaryPath _ _
  | deviceLogRate x => exact measurable_id
  | deviceWander x k => exact measurable_stationaryPath _ _
  | reportError x => exact measurable_stationaryPath _ _
  | jitterCount i j => exact measurable_pi_iff.mpr fun t => GenerativeWorld.measurable_pausedPath t
  | jitterLevel i j =>
    exact measurable_pi_iff.mpr fun n => (measurable_pi_apply n).max measurable_const
  | linkPaused i j => exact GenerativeWorld.measurable_tamePath
  | outage i j => exact GenerativeWorld.measurable_tamePath
  | dropped i j q => exact measurable_id
  | hostPaused h => exact GenerativeWorld.measurable_tamePath

theorem canonicalDraw_part (f : Member H R) (o : Orientation H) (p : Part H R)
    (y : ∀ p : Part H R, p.Coordinate) :
    (canonicalDraw f y).part o p = partMap f o p (y p) := by
  cases p with
  | split z => exact GenerativeWorld.canonicalDraw_component o (.split z) (splitCoordinates y)
  | offset h => rfl
  | logRate h => rfl
  | wander h k => rfl
  | deviceLogRate x => rfl
  | deviceWander x k => rfl
  | reportError x => rfl
  | jitterCount i j => rfl
  | jitterLevel i j => rfl
  | linkPaused i j => rfl
  | outage i j => rfl
  | dropped i j q => rfl
  | hostPaused h => rfl

end Draw


/-! ## Episodes read from an outcome -/

section Episodes

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → Cells} {r : ℝ}
  {F : Measure ℝ} [IsProbabilityMeasure F]

/-- The path of the cells of a random outcome is a path of episodes, when
the episodes take less than all of the time on average. -/
theorem isEpisodePath_tamePath (hr : 0 ≤ r) (hF : F (Set.Iic 0) = 0)
    (hmean : Integrable (fun x : ℝ => x) F) (hload : r * ∫ x, x ∂F < 1)
    (hZ : MeasurePreserving Z P (cellsLaw (Real.toNNReal r) F)) :
    IsEpisodePath r F (fun t ω => tamePath (Z ω) t) P where
  zero := fun _ => GenerativeWorld.tamePath_zero _
  monotone := fun _ => GenerativeWorld.tamePath_monotone _
  rightContinuous := fun _ t => GenerativeWorld.tamePath_rightContinuous _ t
  increments := GenerativeWorld.hasIndepIncrements_tamePath hr hF hmean hload hZ
  law := fun _ _ hst => GenerativeWorld.hasLaw_tamePath_sub hr hF hmean hload hZ hst

/-- The path of the cells of a random outcome is a path of episodes,
whatever their rate. -/
theorem isEpisodePath_pausedPath (hr : 0 ≤ r) (hF : F (Set.Iic 0) = 0)
    (hZ : MeasurePreserving Z P (cellsLaw (Real.toNNReal r) F)) :
    IsEpisodePath r F (fun t ω => pausedPath (Z ω) t) P where
  zero := fun _ => GenerativeWorld.pausedPath_zero _
  monotone := fun _ => GenerativeWorld.pausedPath_monotone _
  rightContinuous := fun _ t => GenerativeWorld.pausedPath_rightContinuous _ t
  increments := by
    intro n t ht
    exact GenerativeWorld.iIndepFun_of_measurePreserving hZ
      (fun i => (GenerativeWorld.measurable_pausedPath _).sub
        (GenerativeWorld.measurable_pausedPath _))
      (GenerativeWorld.hasIndepIncrements_pausedPath (Real.toNNReal r) F hF n t ht)
  law := fun s t hst => by
    have h := GenerativeWorld.hasLaw_pausedPath_sub (Real.toNNReal r) F hF hst
    rw [Real.coe_toNNReal r hr] at h
    exact h.fun_comp hZ.hasLaw

end Episodes

/-! ## The law of the draw of an outcome -/

section Prior

variable [DecidableEq H]

/-- **The draw of an outcome has the law of the member.** -/
theorem canonicalDraw_prior (m : Told H R) (f : Member H R) :
    Prior m f (Measure.infinitePi (partLaw m f)) (canonicalDraw (H := H) (R := R) f) where
  prob := inferInstance
  split_swap := fun y => GenerativeWorld.canonicalDraw_split_swap (splitCoordinates y)
  split_mem := fun y => GenerativeWorld.canonicalDraw_split_mem (splitCoordinates y)
  split_law := fun i j hij =>
    GenerativeWorld.hasLaw_canonicalDraw_split m.shape hij
      (Y := fun y : ∀ p : Part H R, p.Coordinate => splitCoordinates y)
      (measurePreserving_eval_infinitePi (partLaw m f) (.split (pairOf i j hij))).hasLaw
  offset_law := fun h => (measurePreserving_eval_infinitePi (partLaw m f) (.offset h)).hasLaw
  logRate_law := fun h => (measurePreserving_eval_infinitePi (partLaw m f) (.logRate h)).hasLaw
  wander_gaussian := fun h k =>
    isGaussianProcess_stationaryPath_comp _ (f.wanderTime_pos h k)
      (measurePreserving_eval_infinitePi (partLaw m f) (.wander h k)).hasLaw
  wander_mean := fun h k t =>
    integral_stationaryPath_comp _ (f.wanderTime_pos h k)
      (measurePreserving_eval_infinitePi (partLaw m f) (.wander h k)).hasLaw t
  wander_covariance := fun h k s t =>
    covariance_stationaryPath_comp _ (f.wanderTime_pos h k)
      (measurePreserving_eval_infinitePi (partLaw m f) (.wander h k)).hasLaw s t
  wander_continuous := fun _ _ _ => continuous_stationaryPath _ _ _
  deviceLogRate_law := fun x =>
    (measurePreserving_eval_infinitePi (partLaw m f) (.deviceLogRate x)).hasLaw
  deviceWander_gaussian := fun x k =>
    isGaussianProcess_stationaryPath_comp _ (f.deviceWanderTime_pos x k)
      (measurePreserving_eval_infinitePi (partLaw m f) (.deviceWander x k)).hasLaw
  deviceWander_mean := fun x k t =>
    integral_stationaryPath_comp _ (f.deviceWanderTime_pos x k)
      (measurePreserving_eval_infinitePi (partLaw m f) (.deviceWander x k)).hasLaw t
  deviceWander_covariance := fun x k s t =>
    covariance_stationaryPath_comp _ (f.deviceWanderTime_pos x k)
      (measurePreserving_eval_infinitePi (partLaw m f) (.deviceWander x k)).hasLaw s t
  deviceWander_continuous := fun _ _ _ => continuous_stationaryPath _ _ _
  reportError_gaussian := fun x =>
    isGaussianProcess_stationaryPath_comp _ (f.reportTime_pos x)
      (measurePreserving_eval_infinitePi (partLaw m f) (.reportError x)).hasLaw
  reportError_mean := fun x t =>
    integral_stationaryPath_comp _ (f.reportTime_pos x)
      (measurePreserving_eval_infinitePi (partLaw m f) (.reportError x)).hasLaw t
  reportError_covariance := fun x s t =>
    covariance_stationaryPath_comp _ (f.reportTime_pos x)
      (measurePreserving_eval_infinitePi (partLaw m f) (.reportError x)).hasLaw s t
  reportError_continuous := fun _ _ => continuous_stationaryPath _ _ _
  jitterCount_law := fun i j =>
    isEpisodePath_pausedPath (f.jitterRate_pos i j).le (by simp)
      (measurePreserving_eval_infinitePi (partLaw m f) (.jitterCount i j))
  jitterLevel_law := fun i j => by
    have h := (measurePreserving_eval_infinitePi (partLaw m f) (.jitterLevel i j)).hasLaw
    refine h.congr ?_
    have hnn : ∀ᵐ y ∂Measure.infinitePi (partLaw m f), ∀ n : ℤ,
        0 ≤ (y (.jitterLevel i j) : ℤ → ℝ) n := by
      rw [ae_all_iff]
      intro n
      have hn : ∀ᵐ u ∂(Measure.infinitePi fun _ : ℤ => f.jitterLaw i j), 0 ≤ u n := by
        have h0 := (measurePreserving_eval_infinitePi (fun _ : ℤ => f.jitterLaw i j) n)
        have h1 : ∀ᵐ x ∂f.jitterLaw i j, 0 ≤ x := by
          rw [ae_iff]
          have : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by
            ext x
            simp
          rw [this]
          exact f.jitterLaw_nonneg i j
        exact h0.quasiMeasurePreserving.ae h1
      exact (measurePreserving_eval_infinitePi (partLaw m f)
        (.jitterLevel i j)).quasiMeasurePreserving.ae hn
    filter_upwards [hnn] with y hy
    funext n
    exact max_eq_left (hy n)
  jitterLevel_nonneg := fun _ _ _ _ => le_max_right _ _
  linkPaused_law := fun i j =>
    have := f.linkPauseLength_prob i j
    isEpisodePath_tamePath (f.linkPauseRate_nonneg i j) (f.linkPauseLength_pos i j)
      (f.linkPauseLength_mean i j) (f.linkLoad_lt_one i j)
      (measurePreserving_eval_infinitePi (partLaw m f) (.linkPaused i j))
  outage_law := fun i j =>
    have := f.outageLength_prob i j
    isEpisodePath_tamePath (f.outageRate_nonneg i j) (f.outageLength_pos i j)
      (f.outageLength_mean i j) (f.outageLoad_lt_one i j)
      (measurePreserving_eval_infinitePi (partLaw m f) (.outage i j))
  dropped_law := fun i j q =>
    (measurePreserving_eval_infinitePi (partLaw m f) (.dropped i j q)).hasLaw
  hostPaused_law := fun h =>
    have := f.hostPauseLength_prob h
    isEpisodePath_tamePath (f.hostPauseRate_nonneg h) (f.hostPauseLength_pos h)
      (f.hostPauseLength_mean h) (f.hostLoad_lt_one h)
      (measurePreserving_eval_infinitePi (partLaw m f) (.hostPaused h))
  independent := fun o => by
    have h : (fun p (y : ∀ p : Part H R, p.Coordinate) => (canonicalDraw f y).part o p)
        = fun p (y : ∀ p : Part H R, p.Coordinate) => partMap f o p (y p) := by
      funext p y
      exact canonicalDraw_part f o p y
    rw [h]
    exact iIndepFun_infinitePi fun p => measurable_partMap f o p

/-- **The draw of almost every outcome is regular.** -/
theorem ae_regular [Countable H] (m : Told H R) (f : Member H R) :
    ∀ᵐ y ∂Measure.infinitePi (partLaw m f), (canonicalDraw (H := H) (R := R) f y).Regular f := by
  have hclock : ∀ᵐ y ∂Measure.infinitePi (partLaw m f), ∀ h : H,
      Tendsto (clockAdvance ((canonicalDraw f y).logRateAt f h)) atTop atTop
        ∧ Tendsto (clockAdvance ((canonicalDraw f y).logRateAt f h)) atBot atBot := by
    rw [ae_all_iff]
    intro h
    refine ae_tendsto_clockAdvance (P := Measure.infinitePi (partLaw m f))
      (c := fun y => (y (.logRate h) : ℝ))
      (X := fun x y => ∑ k ∈ Finset.range f.scales,
        stationaryPath (f.wanderSize h k) (f.wanderTime h k) (y (.wander h k)) x)
      (K := ∑ k ∈ Finset.range f.scales, (1 + f.wanderSize h k ^ 2) / 2)
      (fun x => Finset.measurable_sum _ fun k _ =>
        (measurable_stationaryPath_apply _ _ x).comp (measurable_pi_apply _))
      (fun y => continuous_finsetSum _ fun k _ => continuous_stationaryPath _ _ _)
      (Finset.sum_nonneg fun k _ => by positivity)
      (fun x => lintegral_abs_sum_le _
        (fun k _ => (measurable_stationaryPath_apply _ _ x).comp (measurable_pi_apply _))
        (fun k _ => by positivity)
        (fun k _ => lintegral_abs_stationaryPath_comp_le _ (f.wanderTime_pos h k)
          (measurePreserving_eval_infinitePi (partLaw m f) (.wander h k)).hasLaw x))
  have hdevice : ∀ᵐ y ∂Measure.infinitePi (partLaw m f), ∀ x : Option (Fin R),
      Tendsto (clockAdvance ((canonicalDraw f y).deviceLogRateAt f x)) atTop atTop
        ∧ Tendsto (clockAdvance ((canonicalDraw f y).deviceLogRateAt f x)) atBot atBot := by
    rw [ae_all_iff]
    intro x
    refine ae_tendsto_clockAdvance (P := Measure.infinitePi (partLaw m f))
      (c := fun y => (y (.deviceLogRate x) : ℝ))
      (X := fun t y => ∑ k ∈ Finset.range f.scales,
        stationaryPath (f.deviceWanderSize x k) (f.deviceWanderTime x k)
          (y (.deviceWander x k)) t)
      (K := ∑ k ∈ Finset.range f.scales, (1 + f.deviceWanderSize x k ^ 2) / 2)
      (fun t => Finset.measurable_sum _ fun k _ =>
        (measurable_stationaryPath_apply _ _ t).comp (measurable_pi_apply _))
      (fun y => continuous_finsetSum _ fun k _ => continuous_stationaryPath _ _ _)
      (Finset.sum_nonneg fun k _ => by positivity)
      (fun t => lintegral_abs_sum_le _
        (fun k _ => (measurable_stationaryPath_apply _ _ t).comp (measurable_pi_apply _))
        (fun k _ => by positivity)
        (fun k _ => lintegral_abs_stationaryPath_comp_le _ (f.deviceWanderTime_pos x k)
          (measurePreserving_eval_infinitePi (partLaw m f) (.deviceWander x k)).hasLaw t))
  filter_upwards [hclock, hdevice] with y hc hdv
  exact
    { split_mem := GenerativeWorld.canonicalDraw_split_mem (splitCoordinates y)
      wander_continuous := fun _ _ => continuous_stationaryPath _ _ _
      deviceWander_continuous := fun _ _ => continuous_stationaryPath _ _ _
      clock_top := fun h => (hc h).1
      clock_bot := fun h => (hc h).2
      device_top := fun x => (hdv x).1
      device_bot := fun x => (hdv x).2
      jitter_nonneg := fun _ _ _ => le_max_right _ _
      linkPaused_monotone := fun _ _ => GenerativeWorld.tamePath_monotone _
      linkPaused_tame := fun _ _ => GenerativeWorld.tamePath_tame _
      hostPaused_monotone := fun _ => GenerativeWorld.tamePath_monotone _
      hostPaused_tame := fun _ => GenerativeWorld.tamePath_tame _ }

/-- **Every member has a random world.** For every member of the model, with
hosts that can be counted, there are a probability space and a random world
on it that belongs to the member. -/
theorem exists_holds [Countable H] (m : Told H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (world : Ω → World H R),
      Holds m f P world := by
  classical
  have hreg := ae_regular (H := H) (R := R) m f
  obtain ⟨y₀, hy₀⟩ := hreg.exists
  let φ : (∀ p : Part H R, p.Coordinate) → ∀ p : Part H R, p.Coordinate := fun y =>
    if (canonicalDraw f y).Regular f then y else y₀
  have hφ : ∀ᵐ y ∂Measure.infinitePi (partLaw m f), φ y = y := by
    filter_upwards [hreg] with y hy
    simp only [φ, hy, ite_true]
  have hall : ∀ y, (canonicalDraw f (φ y)).Regular f := by
    intro y
    by_cases hy : (canonicalDraw f y).Regular f
    · simp only [φ, hy, ite_true]
    · simpa only [φ, hy, ite_false] using hy₀
  exact ⟨_, inferInstance, Measure.infinitePi (partLaw m f),
    fun y => drawWorld m f hex (canonicalDraw f (φ y)) (hall y),
    fun y => canonicalDraw f (φ y), (canonicalDraw_prior m f).comp_ae_eq hφ,
    fun y => drawWorld_builds m f hex _ (hall y)⟩

end Prior

end Unisono.Spec.ProposedWorld
