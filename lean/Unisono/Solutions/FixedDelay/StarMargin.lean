/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Arrivals
public import Unisono.Solutions.FixedDelay.Exact
public import Unisono.Solutions.FixedDelay.Speed
public import Unisono.Spec.Models.GenerativeStar

/-!
# A bound for the baseline against solutions through the sender

In the noiseless members of the generative model, with any number of hosts
and speakers, the baseline's expected cost exceeds that of no compared star
solution by more than a known margin (`within_starMargin`). A star solution is
one whose hosts exchange messages only with the sender. The theorem is
stated for every member of the model: for every other member its margin is
`⊤`, and it says nothing about them.

* **The members.** `NoiselessWithMargin`: the noiseless members in which the
  target latency exceeds the baseline's delivery margin for every speaker;
  and `MissedWeightPays`: those in which the weight of missed samples is
  large enough that not playing frames does not pay.
* **The compared solutions.** `StarSolutions`
  (`Unisono.Spec.Models.GenerativeStar`): the star solutions with measurable
  cost whose position advances by one frame per output sample within a
  bound `u < 1`, in every step of continuous playback. The baseline is one
  of them when its slew is at most `u`.
* **The margin.** `starMargin`: the sum of the weights of synchronization
  and of tracking, times `ρ ^ 3 / (4 * Θ)`, where `ρ` is the sum, over the
  speakers, of the least round-trip time between the sender and the
  speaker's host, and `Θ` is the bound of the clock offsets.

The baseline's cost in almost every outcome is the shift cost of the
asymmetries of the speakers' hosts (`ae_cost_eq`). The asymmetry of a host is
how far the least delay from the sender to it exceeds half the least
round-trip time between the two. No compared solution pays less than the
mean cost of the asymmetries of those hosts whose reflection keeps the clock
offset within its range (`StarSolutions.le_expectedCost`);
the margin covers the outcomes in which some host's reflection does not
(`lintegral_asymmetry_le`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

theorem measurable_shiftCost (c : Weights) :
    Measurable fun x : Fin R → ℝ => shiftCost c x := by
  have h : Continuous fun x : Fin R → ℝ => shiftCost c x := by
    unfold shiftCost varFin meanFin
    fun_prop
  exact h.measurable

/-- What a shift costs through one speaker is at most the weight of tracking
plus four times the weight of synchronization, times the square of the
largest shift. -/
theorem speakerShiftCost_le (c : Weights) (hR : 0 < R) {x : Fin R → ℝ} {B : ℝ}
    (hx : ∀ r, |x r| ≤ B) (r : Fin R) :
    speakerShiftCost c x r ≤ ((c.tracking : ℝ) + 4 * (c.sync : ℝ)) * B ^ 2 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have h1 : x r ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx r) 2
  have h2 : (∑ r', (x r - x r') ^ 2) / R ≤ 4 * B ^ 2 := by
    rw [div_le_iff₀ hRpos]
    calc ∑ r', (x r - x r') ^ 2 ≤ ∑ _r' : Fin R, 4 * B ^ 2 :=
          Finset.sum_le_sum fun r' _ => by
            have ha := abs_le.mp (hx r)
            have hb := abs_le.mp (hx r')
            have h3 : |x r - x r'| ≤ 2 * B := by
              rw [abs_le]
              constructor <;> linarith
            calc (x r - x r') ^ 2 = |x r - x r'| ^ 2 := (sq_abs _).symm
              _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
              _ = 4 * B ^ 2 := by ring
      _ = 4 * B ^ 2 * R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  unfold speakerShiftCost
  have hs : (0 : ℝ) ≤ c.sync := c.sync.coe_nonneg
  have ht : (0 : ℝ) ≤ c.tracking := c.tracking.coe_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h1 ht, mul_le_mul_of_nonneg_left h2 hs]

/-- The uniform law between `-Θ` and `Θ` gives the numbers within `τ` of the
two ends a probability of at most `τ / Θ`. -/
theorem cond_volume_Icc_compl_le {Θ τ : ℝ} (hΘ : 0 < Θ) (hτ : 0 ≤ τ) :
    ProbabilityTheory.cond volume (Set.Icc (-Θ) Θ) (Set.Icc (-(Θ - τ)) (Θ - τ))ᶜ
      ≤ ENNReal.ofReal (τ / Θ) := by
  rw [ProbabilityTheory.cond_apply measurableSet_Icc, Real.volume_Icc]
  have hsub : Set.Icc (-Θ) Θ ∩ (Set.Icc (-(Θ - τ)) (Θ - τ))ᶜ
      ⊆ Set.Icc (-Θ) (-(Θ - τ)) ∪ Set.Icc (Θ - τ) Θ := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    by_cases hx : x < -(Θ - τ)
    · exact Or.inl ⟨h1, hx.le⟩
    · refine Or.inr ⟨?_, h2⟩
      by_contra hc
      exact h3 ⟨not_lt.mp hx, (not_le.mp hc).le⟩
  have e1 : -(Θ - τ) - -Θ = τ := by ring
  have e2 : Θ - (Θ - τ) = τ := by ring
  have hvol : volume (Set.Icc (-Θ) Θ ∩ (Set.Icc (-(Θ - τ)) (Θ - τ))ᶜ)
      ≤ ENNReal.ofReal (2 * τ) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Icc, Real.volume_Icc, e1, e2, ← ENNReal.ofReal_add hτ hτ]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hΘ2 : (0 : ℝ) < Θ - -Θ := by linarith
  have hreal : (Θ - -Θ)⁻¹ * (2 * τ) = τ / Θ := by
    have := hΘ.ne'
    field_simp
    ring
  calc (ENNReal.ofReal (Θ - -Θ))⁻¹ * volume (Set.Icc (-Θ) Θ ∩ (Set.Icc (-(Θ - τ)) (Θ - τ))ᶜ)
      ≤ (ENNReal.ofReal (Θ - -Θ))⁻¹ * ENNReal.ofReal (2 * τ) := by gcongr
    _ = ENNReal.ofReal (τ / Θ) := by
        rw [← ENNReal.ofReal_inv_of_pos hΘ2, ← ENNReal.ofReal_mul (inv_nonneg.mpr hΘ2.le),
          hreal]

namespace GenerativeWorld

/-- Each split of a draw is a measurable function of the draw. -/
theorem Draw.measurable_split (i j : H) : Measurable fun d : Draw H R => d.split i j := by
  have hT : Measurable fun d : Draw H R =>
      (d.split, d.offset, d.logRate, d.wander, d.linkPaused, d.hostPaused,
        d.deviceLogRate, d.deviceWander, d.reportError) :=
    comap_measurable _
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_fst.comp hT))

/-- The asymmetry of host `h` in a draw: how far the least delay from the
sender to `h` exceeds half the least round-trip time between the two. A
round-trip estimate of the sender's clock at `h` is off by this amount. -/
def Draw.asymmetry (d : Draw H R) (m : GenerativeWorld H R) (f : Member H R) (h : H) : ℝ :=
  (d.split m.sender h - 1 / 2) * f.roundTrip m.sender h

theorem Draw.measurable_asymmetry (m : GenerativeWorld H R) (f : Member H R) (h : H) :
    Measurable fun d : Draw H R => d.asymmetry m f h :=
  ((Draw.measurable_split m.sender h).sub_const _).mul_const _

/-- The noiseless members in which the target latency exceeds the baseline's
delivery margin for every speaker: the spans of the resampler's lookahead and
of two blocks, half the least round-trip time between the sender and the
speaker's host, and the request lead. -/
structure NoiselessWithMargin (m : GenerativeWorld H R) (lookahead : ℕ+) (f : Member H R) :
    Prop where
  noiseless : f.Noiseless
  margin : ∀ r, (((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate
    + f.roundTrip m.sender (m.host r) / 2 + m.lead < m.targetLatency

/-- The sum, over the speakers, of the least round-trip time between the
sender and the speaker's host. -/
def Member.roundTripSum (f : Member H R) (m : GenerativeWorld H R) : ℝ :=
  ∑ r : Fin R, f.roundTrip m.sender (m.host r)

/-- The margin of the bound for the baseline against solutions through
the sender: the sum of the weights of synchronization and of tracking, times
`ρ ^ 3 / (4 * Θ)`, where `ρ` is `f.roundTripSum m` and `Θ` is the bound of
the clock offsets. -/
def starMargin (m : GenerativeWorld H R) (f : Member H R) (c : Weights) : ℝ≥0∞ :=
  ENNReal.ofReal (((c.sync : ℝ) + (c.tracking : ℝ)) * (f.roundTripSum m / 2) ^ 2
    * (f.roundTripSum m / f.offsetRange))

/-- The members in which the weight of missed samples is large enough that
no solution through the sender within the speed bound `u` gains by not
playing frames. Six times the largest cost of a shift through one speaker
(the weight of tracking plus four times the weight of synchronization, times
the square of half of `f.roundTripSum m`) is at most the weight of missed
samples times `1 - u` times the rate. -/
def MissedWeightPays (m : GenerativeWorld H R) (f : Member H R) (c : Weights) (u : ℝ) : Prop :=
  6 * (((c.tracking : ℝ) + 4 * (c.sync : ℝ)) * (f.roundTripSum m / 2) ^ 2)
    ≤ (c.missed : ℝ) * (1 - u) * m.rate

section Margin

variable [DecidableEq H]

/-- The asymmetry of a host is at most half the least round-trip time between
the sender and the host. -/
theorem abs_asymmetry_le (m : GenerativeWorld H R) (f : Member H R) (y : Component H R → ℝ)
    (h : H) : |(canonicalDraw y).asymmetry m f h| ≤ f.roundTrip m.sender h / 2 := by
  have hmem := canonicalDraw_split_mem y m.sender h
  have hτ := f.roundTrip_pos m.sender h
  have h1 : |(canonicalDraw y).split m.sender h - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  unfold Draw.asymmetry
  rw [abs_mul, abs_of_pos hτ]
  have h2 := mul_le_mul_of_nonneg_right h1 hτ.le
  linarith

/-- The reflection of a receiving host moves its offset by twice its
asymmetry. -/
theorem reflectScale_mul (m : GenerativeWorld H R) (f : Member H R) (k : m.ReceivingHost)
    (y : Component H R → ℝ) :
    reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
      = 2 * (canonicalDraw y).asymmetry m f k.1 := by
  have hsh : m.sender ≠ k.1 := k.2.symm
  have hs : (canonicalDraw y).split m.sender k.1
      = if (refOrientation H (pairOf m.sender k.1 hsh)).1 = (m.sender, k.1) then
          splitOf (y (.split (pairOf m.sender k.1 hsh)))
        else 1 - splitOf (y (.split (pairOf m.sender k.1 hsh))) := by
    simp only [canonicalDraw, dite_eq_right hsh]
  unfold Draw.asymmetry reflectScale senderSplit
  rw [hs]
  by_cases ho : (refOrientation H (pairOf m.sender k.1 hsh)).1 = (m.sender, k.1)
  · rw [ite_eq_left ho, ite_eq_left ho]
    ring
  · rw [ite_eq_right ho, ite_eq_right ho]
    ring

variable [Fintype H]

/-- When the reflection of a receiving host keeps the offset of its clock
within the range, half the shift of the host's timeline is the opposite of
its asymmetry. -/
theorem reflectShift_of_mem (m : GenerativeWorld H R) (f : Member H R) (k : m.ReceivingHost)
    (y : Component H R → ℝ)
    (hy : y (.offset k.1) ∈ Set.Icc (-f.offsetRange) f.offsetRange
      ∧ y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
        ∈ Set.Icc (-f.offsetRange) f.offsetRange) :
    reflectShift m f y k.1 / 2 = -(canonicalDraw y).asymmetry m f k.1 := by
  obtain ⟨-, e2⟩ := reflect_apply m f k y
  have hval : (reflectPair (reflectScale m f k) f.offsetRange
      (y (m.senderSplit k), y (.offset k.1))).2
      = y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2) := by
    show (if y (.offset k.1) ∈ Set.Icc (-f.offsetRange) f.offsetRange
          ∧ y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
            ∈ Set.Icc (-f.offsetRange) f.offsetRange then
        ((1 - y (m.senderSplit k),
          y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)) :
            ℝ × ℝ)
      else (y (m.senderSplit k), y (.offset k.1))).2 = _
    rw [ite_eq_left hy]
  rw [reflectShift, e2, hval, reflectScale_mul]
  ring

/-- The reflection shifts the timeline of a receiving host by at most the
least round-trip time between the sender and the host. -/
theorem abs_reflectShift_le (m : GenerativeWorld H R) (f : Member H R) (k : m.ReceivingHost)
    (y : Component H R → ℝ) : |reflectShift m f y k.1| ≤ f.roundTrip m.sender k.1 := by
  by_cases hy : y (.offset k.1) ∈ Set.Icc (-f.offsetRange) f.offsetRange
      ∧ y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
        ∈ Set.Icc (-f.offsetRange) f.offsetRange
  · have h := reflectShift_of_mem m f k y hy
    have ha := abs_asymmetry_le m f y k.1
    have e : reflectShift m f y k.1 = -(2 * (canonicalDraw y).asymmetry m f k.1) := by
      linarith
    rw [e, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · obtain ⟨-, e2⟩ := reflect_apply m f k y
    have hval : (reflectPair (reflectScale m f k) f.offsetRange
        (y (m.senderSplit k), y (.offset k.1))).2 = y (.offset k.1) := by
      show (if y (.offset k.1) ∈ Set.Icc (-f.offsetRange) f.offsetRange
            ∧ y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
              ∈ Set.Icc (-f.offsetRange) f.offsetRange then
          ((1 - y (m.senderSplit k),
            y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)) :
              ℝ × ℝ)
        else (y (m.senderSplit k), y (.offset k.1))).2 = _
      rw [ite_eq_right hy]
    rw [reflectShift, e2, hval, sub_self, abs_zero]
    exact (f.roundTrip_pos _ _).le

/-- **In a member in which the weight of missed samples pays, it pays in
every outcome**: six times the cost, through any one speaker, of half the
shifts of the reflection is at most the weight of missed samples times
`1 - u` times the rate. -/
theorem MissedWeightPays.threshold {m : GenerativeWorld H R} {f : Member H R} {c : Weights}
    {u : ℝ} (hpay : m.MissedWeightPays f c u) (hnos : ∀ r, m.host r ≠ m.sender) (hR : 0 < R)
    (y : Component H R → ℝ) (r : Fin R) :
    6 * speakerShiftCost c (fun r => reflectShift m f y (m.host r) / 2) r
      ≤ (c.missed : ℝ) * (1 - u) * m.rate := by
  have hτle : ∀ r, f.roundTrip m.sender (m.host r) ≤ f.roundTripSum m := fun r =>
    Finset.single_le_sum (f := fun r => f.roundTrip m.sender (m.host r))
      (fun r _ => (f.roundTrip_pos _ _).le) (Finset.mem_univ r)
  have hx : ∀ r, |reflectShift m f y (m.host r) / 2| ≤ f.roundTripSum m / 2 := fun r => by
    have h := abs_reflectShift_le m f ⟨m.host r, hnos r⟩ y
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h' : |reflectShift m f y (m.host r)| ≤ f.roundTripSum m := h.trans (hτle r)
    linarith
  have h := speakerShiftCost_le c hR hx r
  unfold MissedWeightPays at hpay
  linarith

/-- The reflection of a receiving host moves the offset of its clock out of
the range with a probability of at most the least round-trip time between the
sender and the host, divided by the bound of the offsets. -/
theorem measure_reflect_out_le (m : GenerativeWorld H R) (f : Member H R)
    (k : m.ReceivingHost) :
    Measure.pi (canonicalLaw m f) {y | ¬(y (.offset k.1) ∈ Set.Icc (-f.offsetRange) f.offsetRange
        ∧ y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
          ∈ Set.Icc (-f.offsetRange) f.offsetRange)}
      ≤ ENNReal.ofReal (f.roundTrip m.sender k.1 / f.offsetRange) := by
  have hτ := f.roundTrip_pos m.sender k.1
  have hsub : {y : Component H R → ℝ |
        ¬(y (.offset k.1) ∈ Set.Icc (-f.offsetRange) f.offsetRange
        ∧ y (.offset k.1) + reflectScale m f k * (splitOf (y (m.senderSplit k)) - 1 / 2)
          ∈ Set.Icc (-f.offsetRange) f.offsetRange)}
      ⊆ (fun y : Component H R → ℝ => y (.offset k.1)) ⁻¹'
          (Set.Icc (-(f.offsetRange - f.roundTrip m.sender k.1))
            (f.offsetRange - f.roundTrip m.sender k.1))ᶜ := by
    intro y hy hin
    apply hy
    obtain ⟨h1, h2⟩ : -(f.offsetRange - f.roundTrip m.sender k.1) ≤ y (.offset k.1)
        ∧ y (.offset k.1) ≤ f.offsetRange - f.roundTrip m.sender k.1 := hin
    have ha := abs_le.mp (abs_asymmetry_le m f y k.1)
    rw [reflectScale_mul]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [ha.1], by linarith [ha.2]⟩⟩
  refine (measure_mono hsub).trans ?_
  rw [(measurePreserving_eval (canonicalLaw m f) (.offset k.1)).measure_preimage
    measurableSet_Icc.compl.nullMeasurableSet]
  exact cond_volume_Icc_compl_le f.offsetRange_pos hτ.le

/-- **The mean cost of the asymmetries exceeds the lower bound for solutions
through the sender by at most the margin.** -/
theorem lintegral_asymmetry_le (m : GenerativeWorld H R) (f : Member H R) (c : Weights)
    (hnos : ∀ r, m.host r ≠ m.sender) (hR : 0 < R) :
    ∫⁻ y, ENNReal.ofReal (shiftCost c fun r => (canonicalDraw y).asymmetry m f (m.host r))
        ∂Measure.pi (canonicalLaw m f)
      ≤ starLowerBound m f c + starMargin m f c := by
  classical
  -- The outcomes in which the reflection of the host of speaker `r` keeps the
  -- offset of its clock within the range.
  let good : Fin R → Set (Component H R → ℝ) := fun r =>
    {y | y (.offset (m.host r)) ∈ Set.Icc (-f.offsetRange) f.offsetRange
      ∧ y (.offset (m.host r)) + reflectScale m f ⟨m.host r, hnos r⟩
          * (splitOf (y (m.senderSplit ⟨m.host r, hnos r⟩)) - 1 / 2)
        ∈ Set.Icc (-f.offsetRange) f.offsetRange}
  have hgood : ∀ r, MeasurableSet (good r) := fun r =>
    (measurableSet_Icc.preimage (measurable_pi_apply _)).inter
      (measurableSet_Icc.preimage ((measurable_pi_apply _).add
        (((measurable_splitOf.comp (measurable_pi_apply _)).sub_const _).const_mul _)))
  have hbad : MeasurableSet (⋃ r, (good r)ᶜ) := MeasurableSet.iUnion fun r => (hgood r).compl
  have hτle : ∀ r, f.roundTrip m.sender (m.host r) ≤ f.roundTripSum m := fun r =>
    Finset.single_le_sum (f := fun r => f.roundTrip m.sender (m.host r))
      (fun r _ => (f.roundTrip_pos _ _).le) (Finset.mem_univ r)
  have hK : ∀ y, shiftCost c (fun r => (canonicalDraw y).asymmetry m f (m.host r))
      ≤ ((c.sync : ℝ) + (c.tracking : ℝ)) * (f.roundTripSum m / 2) ^ 2 := fun y =>
    shiftCost_le c hR fun r => (abs_asymmetry_le m f y _).trans (by linarith [hτle r])
  have hK0 : 0 ≤ ((c.sync : ℝ) + (c.tracking : ℝ)) * (f.roundTripSum m / 2) ^ 2 :=
    mul_nonneg (add_nonneg c.sync.coe_nonneg c.tracking.coe_nonneg) (sq_nonneg _)
  -- In every outcome, the cost of the asymmetries is at most the cost of half
  -- the shifts of the reflection, plus the largest cost where some host's
  -- reflection leaves the range.
  have hpt : ∀ y,
      ENNReal.ofReal (shiftCost c fun r => (canonicalDraw y).asymmetry m f (m.host r))
        ≤ ENNReal.ofReal (shiftCost c fun r => reflectShift m f y (m.host r) / 2)
          + (⋃ r, (good r)ᶜ).indicator (fun _ => ENNReal.ofReal
              (((c.sync : ℝ) + (c.tracking : ℝ)) * (f.roundTripSum m / 2) ^ 2)) y := by
    intro y
    by_cases hy : y ∈ ⋃ r, (good r)ᶜ
    · rw [Set.indicator_of_mem hy]
      exact (ENNReal.ofReal_le_ofReal (hK y)).trans le_add_self
    · have hall : ∀ r, y ∈ good r := fun r => by
        by_contra h
        exact hy (Set.mem_iUnion.mpr ⟨r, h⟩)
      have hfun : (fun r => reflectShift m f y (m.host r) / 2)
          = fun r => -(canonicalDraw y).asymmetry m f (m.host r) :=
        funext fun r => reflectShift_of_mem m f ⟨m.host r, hnos r⟩ y (hall r)
      rw [Set.indicator_of_notMem hy, add_zero, hfun, shiftCost_neg]
  have hprob : Measure.pi (canonicalLaw m f) (⋃ r, (good r)ᶜ)
      ≤ ENNReal.ofReal (f.roundTripSum m / f.offsetRange) := by
    refine (measure_iUnion_le _).trans ?_
    rw [tsum_fintype, Member.roundTripSum, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
      fun r _ => div_nonneg (f.roundTrip_pos _ _).le f.offsetRange_pos.le]
    exact Finset.sum_le_sum fun r _ => measure_reflect_out_le m f ⟨m.host r, hnos r⟩
  calc ∫⁻ y, ENNReal.ofReal (shiftCost c fun r => (canonicalDraw y).asymmetry m f (m.host r))
        ∂Measure.pi (canonicalLaw m f)
      ≤ ∫⁻ y, (ENNReal.ofReal (shiftCost c fun r => reflectShift m f y (m.host r) / 2)
          + (⋃ r, (good r)ᶜ).indicator (fun _ => ENNReal.ofReal
              (((c.sync : ℝ) + (c.tracking : ℝ)) * (f.roundTripSum m / 2) ^ 2)) y)
          ∂Measure.pi (canonicalLaw m f) := lintegral_mono hpt
    _ = starLowerBound m f c
          + ENNReal.ofReal (((c.sync : ℝ) + (c.tracking : ℝ)) * (f.roundTripSum m / 2) ^ 2)
            * Measure.pi (canonicalLaw m f) (⋃ r, (good r)ᶜ) := by
        rw [lintegral_add_right' _ (measurable_const.indicator hbad).aemeasurable,
          lintegral_indicator_const hbad]
        rfl
    _ ≤ starLowerBound m f c + starMargin m f c := by
        gcongr
        rw [starMargin, ENNReal.ofReal_mul hK0]
        gcongr

end Margin

end GenerativeWorld

end Unisono.Spec

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec Unisono.Spec.GenerativeWorld MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {lookahead : ℕ+} {c : Weights}

/-- The baseline is configured for the generative model `m`: it has the
model's sender and nominal rate, sends the stream to every speaker's host,
plays at the target latency, sends each message at least once, and has a
slew between zero and one. -/
structure Params.Fits (p : Params H) (m : GenerativeWorld H R) : Prop where
  sender : p.sender = m.sender
  rate : p.rate = m.rate
  speakers : ∀ r, m.host r ∈ p.speakers
  nodup : p.speakers.Nodup
  latency : p.latency = m.targetLatency
  copies : 0 < p.copies
  period : 0 ≤ p.period
  slew_pos : 0 < p.slew
  slew_lt : p.slew < 1

variable [Fintype H]

/-- The asymmetry of a host in the ideal constant world model of an outcome
is the asymmetry of the host in the outcome's draw. -/
theorem asymmetry_idealWorld (hf : f.Noiseless) (y : Component H R → ℝ) (h : H) :
    ((canonicalDraw_prior m f hf).idealWorld y).asymmetry h
      = (canonicalDraw y).asymmetry m f h := by
  have h1 := canonicalDraw_split_swap y m.sender h
  show ((canonicalDraw y).split m.sender h * f.roundTrip m.sender h
      - (canonicalDraw y).split h m.sender * f.roundTrip h m.sender) / 2
    = ((canonicalDraw y).split m.sender h - 1 / 2) * f.roundTrip m.sender h
  rw [f.roundTrip_symm h m.sender]
  linear_combination (-(f.roundTrip m.sender h) / 2) * h1

omit [Fintype H] in
/-- The delivery margin of a member, for the two least delays between the
sender and a speaker's host in an outcome. -/
theorem margin_idealWorld (hmem : m.NoiselessWithMargin lookahead f) (y : Component H R → ℝ)
    (r : Fin R) :
    (((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate
      + ((canonicalDraw y).split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
        + (canonicalDraw y).split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
      + m.lead < m.targetLatency := by
  have h1 := canonicalDraw_split_swap y m.sender (m.host r)
  have h2 := hmem.margin r
  have e : (canonicalDraw y).split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
      + (canonicalDraw y).split (m.host r) m.sender * f.roundTrip m.sender (m.host r)
      = f.roundTrip m.sender (m.host r) := by
    linear_combination f.roundTrip m.sender (m.host r) * h1
  rw [f.roundTrip_symm (m.host r) m.sender, e]
  exact h2

/-- In almost every outcome of a noiseless member, the world is an ideal
constant world. -/
theorem ae_idealWorld (hf : f.Noiseless) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    ∀ᵐ y ∂Measure.pi (canonicalLaw m f),
      ((canonicalDraw_prior m f hf).idealWorld y).Holds (canonicalWorld m f hex y) := by
  filter_upwards [(canonicalDraw_prior m f hf).ae_idealConstantWorld hf
    (canonicalWorld_builds m f hex)] with y h1
  exact h1.1

/-- **The baseline's cost in almost every outcome** is the shift cost of the
asymmetries of the speakers' hosts. -/
theorem ae_cost_eq (p : Params H) (hp : p.Fits m) (hnos : ∀ r, m.host r ≠ m.sender)
    (hmem : m.NoiselessWithMargin lookahead f) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h)
    (hcl : c.latency = 0) (hcr : c.roughness = 0) (hR : 0 < R) :
    ∀ᵐ y ∂Measure.pi (canonicalLaw m f),
      (solution p : Solution H R Payload).cost (canonicalWorld m f hex y) lookahead c
        = ENNReal.ofReal
            (shiftCost c fun r => (canonicalDraw y).asymmetry m f (m.host r)) := by
  filter_upwards [ae_idealWorld hmem.noiseless hex] with y hy
  rw [cost_eq_of_ideal p _ _ hy hnos lookahead c hcl hcr hp.sender hp.rate hp.speakers
    hp.nodup hp.latency hp.copies hp.period hp.slew_pos hp.slew_lt
    (margin_idealWorld hmem y) hR]
  congr 2
  funext r
  exact asymmetry_idealWorld hmem.noiseless y (m.host r)

/-- **The baseline is one of the compared solutions** at every noiseless
member within the delivery margin, for every speed bound that is at least its
slew. -/
theorem starSolutions (p : Params H) (hp : p.Fits m) (hnos : ∀ r, m.host r ≠ m.sender)
    (hmem : m.NoiselessWithMargin lookahead f) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h)
    (hcl : c.latency = 0) (hcr : c.roughness = 0) (hR : 0 < R) {u : ℝ} (hslew : p.slew ≤ u) :
    m.StarSolutions f lookahead c u Payload (solution p) where
  star := by
    have h := fixedDelay_isStar (R := R) p
    rw [hp.sender] at h
    exact h
  measurable :=
    ⟨fun d => ENNReal.ofReal (shiftCost c fun r => d.asymmetry m f (m.host r)),
      ENNReal.measurable_ofReal.comp ((measurable_shiftCost c).comp
        (Measurable.of_eval fun r => Draw.measurable_asymmetry m f (m.host r))),
      fun _ _ _ _ _ hD hB => hD.ae_of_ae_canonicalDraw hmem.noiseless hB hex
        (p := fun d w => (solution p : Solution H R Payload).cost w lookahead c
          = ENNReal.ofReal (shiftCost c fun r => d.asymmetry m f (m.host r)))
        (ae_cost_eq p hp hnos hmem hex hcl hcr hR)⟩
  withinStep := fun _ _ _ _ world _ _ =>
    Filter.Eventually.of_forall fun ω => withinStep p (world ω) lookahead hp.slew_pos.le hslew

open Classical in
/-- **The baseline against solutions through the sender within a speed
bound, within a known margin.** Consider a generative model in which no
speaker is on the sender's host, weights with no weight on latency or
roughness, and a speed bound `u < 1` that is at least the baseline's slew.
Let the baseline be configured for the model. Take the noiseless members
within the delivery margin in which the weight of missed samples pays
(`MissedWeightPays`). In every random world of each of them, with any number
of hosts and speakers, the baseline's expected cost exceeds that of no star
solution compared at that member by more than `starMargin`. The compared
solutions are the star solutions with measurable cost whose position
advances by one frame per output sample within `u`; nothing is assumed about
which frames they play. The
statement is about every member of the model: for every other member the
margin is `⊤`, and the theorem says nothing about it. -/
theorem within_starMargin (p : Params H) (hp : p.Fits m) (hnos : ∀ r, m.host r ≠ m.sender)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (hcl : c.latency = 0)
    (hcr : c.roughness = 0) (hR : 0 < R) {u : ℝ} (hslew : p.slew ≤ u) (hu : u < 1) :
    m.OptimalWithin (fun f => m.StarSolutions f lookahead c u) lookahead c
      (fun f => if m.NoiselessWithMargin lookahead f ∧ m.MissedWeightPays f c u then
        starMargin m f c else ⊤)
      (solution p : Solution H R Payload) := by
  have hu0 : 0 ≤ u := hp.slew_pos.le.trans hslew
  refine ⟨fun f hε => ?_, fun f Ω _ P world hW Msg' τ hτ => ?_⟩
  · by_cases hmem : m.NoiselessWithMargin lookahead f ∧ m.MissedWeightPays f c u
    · exact starSolutions p hp hnos hmem.1 hex hcl hcr hR hslew
    · exact (hε (ite_eq_right hmem)).elim
  · beta_reduce
    by_cases hmem : m.NoiselessWithMargin lookahead f ∧ m.MissedWeightPays f c u
    · have hσ := starSolutions (c := c) p hp hnos hmem.1 hex hcl hcr hR hslew
      have hf := hmem.1.noiseless
      have hW' : m.Holds f P world := hW
      rw [ite_eq_left hmem]
      calc (solution p : Solution H R Payload).expectedCost P world lookahead c
          = ∫⁻ y, (solution p : Solution H R Payload).cost (canonicalWorld m f hex y)
                lookahead c ∂Measure.pi (canonicalLaw m f) :=
            expectedCost_eq_canonical hσ.measurable hf hex hW'
        _ = ∫⁻ y, ENNReal.ofReal
                (shiftCost c fun r => (canonicalDraw y).asymmetry m f (m.host r))
              ∂Measure.pi (canonicalLaw m f) :=
            lintegral_congr_ae (ae_cost_eq p hp hnos hmem.1 hex hcl hcr hR)
        _ ≤ starLowerBound m f c + starMargin m f c := lintegral_asymmetry_le m f c hnos hR
        _ ≤ τ.expectedCost P world lookahead c + starMargin m f c := by
            gcongr
            exact hτ.le_expectedCost hf hex hR hu0 hu
              (fun y r => hmem.2.threshold hnos hR y r) hW'
    · rw [ite_eq_right hmem, add_top]
      exact le_top

/-! ## The conditions of the theorem can be met -/

section Example

/-- The example's model: three hosts, the sender and two speakers on their
own hosts, devices at one frame per second in blocks of one frame, a request
lead of half a second, a target latency of three seconds, and shape two. -/
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

/-- The example's member: round trips of one second, no pauses, no wander
and no spread of the clocks' mean rates. -/
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

/-- The example's baseline: it sends the stream to both speakers' hosts and
plays at the target latency of three seconds. -/
private def exampleParams : Params (Fin 3) where
  sender := 0
  speakers := [1, 2]
  rate := 1
  latency := 3
  copies := 1
  period := 1
  slew := 1 / 2

/-- The example's weights: one on synchronization and on tracking, sixty on
missed samples, none on the other objectives. -/
private def exampleWeights : Weights where
  sync := 1
  latency := 0
  tracking := 1
  roughness := 0
  missed := 60
  discontinuities := 0

/-- **The conditions of `within_starMargin` can be met.** There are a generative
model, a configuration of the baseline, weights, a speed bound and a
noiseless member within the delivery margin in which the weight of missed
samples pays, with a random world, that satisfy the conditions of the
theorem. -/
theorem within_starMargin_conditions :
    ∃ (m : GenerativeWorld (Fin 3) 2) (p : Params (Fin 3)) (f : Member (Fin 3) 2)
        (c : Weights) (u : ℝ),
      p.Fits m ∧ (∀ r, m.host r ≠ m.sender) ∧ (∀ h, h = m.sender ∨ ∃ r, m.host r = h)
        ∧ c.latency = 0 ∧ c.roughness = 0 ∧ p.slew ≤ u ∧ u < 1
        ∧ m.NoiselessWithMargin 1 f ∧ m.MissedWeightPays f c u
        ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (world : Ω → World (Fin 3) 2),
            m.Holds f P world := by
  have hf : exampleMember.Noiseless :=
    ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
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
  have hfits : exampleParams.Fits exampleModel :=
    { sender := rfl
      rate := rfl
      speakers := hspeakers
      nodup := hnodup
      latency := rfl
      copies := Nat.one_pos
      period := zero_le_one
      slew_pos := by norm_num [exampleParams]
      slew_lt := by norm_num [exampleParams] }
  have hmargin : exampleModel.NoiselessWithMargin 1 exampleMember :=
    ⟨hf, fun r => by
      simp only [exampleModel, exampleMember]
      norm_num⟩
  have hpays : exampleModel.MissedWeightPays exampleMember exampleWeights (1 / 2) := by
    simp only [GenerativeWorld.MissedWeightPays, Member.roundTripSum, exampleModel,
      exampleMember, exampleWeights, Fin.sum_univ_two]
    norm_num
  exact ⟨exampleModel, exampleParams, exampleMember, exampleWeights, 1 / 2, hfits, hnos, hex,
    rfl, rfl, le_rfl, by norm_num, hmargin, hpays, exists_holds_of_noiseless _ _ hf hex⟩

end Example

end Unisono.Solutions.FixedDelay
