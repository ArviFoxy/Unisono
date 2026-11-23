/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Latency
public import Unisono.Solutions.FixedDelay.Progress
public import Unisono.Spec.ExactCost

/-!
# The baseline's exact cost in an ideal constant world

In an ideal constant world with any number of receiving hosts, the baseline
with a latency equal to the target latency plays every frame late, at each
speaker, by the *asymmetry* of that speaker's host: half the difference
between the delay from the sender to the host and the delay back
(`IdealConstantWorld.asymmetry`). Its cost is therefore at most the weight of
synchronization times the spread of the asymmetries over the speakers, plus
the weight of tracking times the mean of their squares (`cost_le_of_ideal`),
when the weights of latency and of roughness are zero.

The reason is that the baseline estimates the sender's clock by the midpoint
of a round trip, which is off by the asymmetry. The proof shifts the timeline
of every receiving host by its asymmetry, along the links to and from the
sender. In the shifted world the two delays between the sender and each host
are equal, the estimates are exact, and every speaker plays at exactly the
baseline's latency (`speaker_at_latency`). The baseline is a star solution
and cannot tell the two worlds apart (`Solution.plays_shiftStarKeepPeers`),
so in the given world each speaker plays every frame late by its host's
asymmetry.

The theorem assumes that no two messages from different hosts arrive at one
host at the same time, because the run breaks such ties by the order of
sending, which a shift can change.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The asymmetry of host `h` in an ideal constant world: half the difference
between the delay from the sender to `h` and the delay from `h` to the
sender. A round-trip estimate of the sender's clock at `h` is off by this
amount. -/
def IdealConstantWorld.asymmetry (m : IdealConstantWorld H R) (h : H) : ℝ :=
  (m.delay m.sender h - m.delay h m.sender) / 2

/-- In an ideal constant world, the output samples of every speaker leave
after every true time. -/
theorem IdealConstantWorld.Holds.out_unbounded {m : IdealConstantWorld H R} {w : World H R}
    (hw : m.Holds w) (r : Fin R) (T : Time) : ∃ k, T ≤ (w.speaker r).out k := by
  obtain ⟨t₀, ht⟩ := hw.speaker_out r
  obtain ⟨k, hk⟩ := exists_nat_ge ((T - t₀) * m.rate)
  refine ⟨k, ?_⟩
  rw [ht, ← sub_le_iff_le_add', le_div_iff₀ m.rate_pos]
  exact hk

/-- In an ideal constant world, frames are captured after every true time. -/
theorem IdealConstantWorld.Holds.capture_unbounded {m : IdealConstantWorld H R}
    {w : World H R} (hw : m.Holds w) (T : Time) : ∃ n, T ≤ w.source.capture n := by
  obtain ⟨t₀, ht⟩ := hw.capture
  obtain ⟨n, hn⟩ := exists_nat_ge ((T - t₀) * m.rate)
  refine ⟨n, ?_⟩
  rw [ht, ← sub_le_iff_le_add', le_div_iff₀ m.rate_pos]
  exact hn

end Unisono.Spec

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec
open scoped ENNReal

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

omit [DecidableEq H] in
/-- In an ideal constant world, when the two delays between the sender and a
host are both `d`, the baseline's fixed-latency playback has no error. -/
theorem latencyError_ideal (m : IdealConstantWorld H R) (rate d : ℝ) :
    latencyError p m.toBounds rate d d = 0 := by
  simp [latencyError, targetError, IdealConstantWorld.toBounds]

/-- **How the baseline plays in an ideal constant world.** Consider an ideal
constant world in which no speaker is on the sender's host. Let the baseline
send the stream to every speaker's host and play at the target latency, with
at least one copy of each message and a slew between zero and one. Let the
target latency exceed, for every speaker, the delivery margin. Suppose that
no two messages from different hosts arrive at one host at the same time.
Then, from some output sample on, every output sample of each speaker plays
the sound captured exactly the target latency plus the asymmetry of the
speaker's host before the sample leaves. -/
theorem playsAtLatencies_of_ideal (m : IdealConstantWorld H R) (w : World H R) (hw : m.Holds w)
    (hnos : ∀ r, m.host r ≠ m.sender) (lookahead : ℕ+)
    (hps : p.sender = m.sender) (hpr : p.rate = m.rate) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hnodup : p.speakers.Nodup) (hpl : p.latency = m.targetLatency) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hslew0 : 0 < p.slew) (hslew1 : p.slew < 1)
    (hlat : ∀ r, (((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate
      + (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2 + m.lead
        < m.targetLatency)
    (hcoll : (solution p : Solution H R Payload).NoCrossOriginCollision w lookahead) :
    ∃ K, w.PlaysAtLatencies ((solution p : Solution H R Payload).plays w lookahead)
      (fun r => p.latency + m.asymmetry (m.host r)) K := by
  classical
  set σ : Solution H R Payload := solution p with hσ
  set Δ : H → ℝ := fun h => if h = m.sender then 0 else m.asymmetry h with hΔ
  have hΔs : Δ m.sender = 0 := by simp [hΔ]
  have hΔh : ∀ h, h ≠ m.sender → Δ h = m.asymmetry h := fun h hh => by simp [hΔ, hh]
  -- Shifting every receiving host back by its asymmetry keeps the delays to
  -- and from the sender positive.
  have hxneg : ∀ i j, (i = m.sender ∨ j = m.sender) → (-Δ) i - (-Δ) j < m.delay i j := by
    intro i j hs
    simp only [Pi.neg_apply]
    rcases hs with rfl | rfl
    · by_cases hj : j = m.sender
      · rw [hj, hΔs]
        linarith [m.delay_pos m.sender m.sender]
      · rw [hΔs, hΔh j hj]
        simp only [IdealConstantWorld.asymmetry]
        linarith [m.delay_pos m.sender j, m.delay_pos j m.sender]
    · by_cases hi : i = m.sender
      · rw [hi, hΔs]
        linarith [m.delay_pos m.sender m.sender]
      · rw [hΔs, hΔh i hi]
        simp only [IdealConstantWorld.asymmetry]
        linarith [m.delay_pos m.sender i, m.delay_pos i m.sender]
  set m₀ := m.starShifted (-Δ) hxneg with hm₀
  set w₀ := shiftStarKeepPeers w (-Δ) (hw.starNet hxneg) with hw₀def
  have hw₀ : m₀.Holds w₀ := hw.shiftStarKeepPeers (by simp [hΔs]) hxneg
  -- In the shifted world both delays between the sender and a speaker's
  -- host are half their round trip.
  have hd0₁ : ∀ r, m₀.delay m.sender (m.host r)
      = (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2 := by
    intro r
    have h1 : m₀.delay m.sender (m.host r)
        = m.delay m.sender (m.host r) + (-Δ) (m.host r) - (-Δ) m.sender := by
      simp [hm₀, IdealConstantWorld.starShifted]
    rw [h1, Pi.neg_apply, Pi.neg_apply, hΔs, hΔh _ (hnos r)]
    simp only [IdealConstantWorld.asymmetry]
    ring
  have hd0₂ : ∀ r, m₀.delay (m.host r) m.sender
      = (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2 := by
    intro r
    have h1 : m₀.delay (m.host r) m.sender
        = m.delay (m.host r) m.sender + (-Δ) m.sender - (-Δ) (m.host r) := by
      simp [hm₀, IdealConstantWorld.starShifted]
    rw [h1, Pi.neg_apply, Pi.neg_apply, hΔs, hΔh _ (hnos r)]
    simp only [IdealConstantWorld.asymmetry]
    ring
  have hwb₀ := IdealConstantWorld.withinBounds hw₀
  have hwb := IdealConstantWorld.withinBounds hw
  have hsend₀ : w₀.sender = m.sender := hw.sender_eq
  have hsender₀ : p.sender = w₀.sender := hps.trans hsend₀.symm
  have hrate₀ : p.rate = w₀.rate := hpr.trans hw.rate_eq.symm
  have hhost₀ : ∀ r, w₀.host r = m.host r := fun r => by
    change w.host r = m.host r
    rw [hw.host_eq]
  -- Each speaker plays at exactly the baseline's latency in the shifted
  -- world.
  have hspeaker : ∀ r, ∃ K, ∀ k, K ≤ k →
      PlaysContinuously (σ.plays w₀ lookahead r) k ∧
        ∃ x, σ.plays w₀ lookahead r k = some x ∧
          |w₀.captured x - ((w₀.speaker r).out k - p.latency)| ≤ 0 := by
    intro r
    have h := speaker_at_latency p w₀ m₀.toBounds hwb₀ lookahead hsender₀ hrate₀ hnodup
      (by simpa [IdealConstantWorld.toBounds] using hcopies) hperiod
      (by rw [hpl]; exact m.targetLatency_nonneg)
      (dmin := (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2)
      (dmax := (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2) r
      (by rw [hhost₀ r]; exact hpsp r)
      (by rw [hhost₀ r, hsend₀]; exact hnos r)
      (by rw [hhost₀ r, hsend₀]; exact (hd0₂ r).ge)
      (by rw [hhost₀ r, hsend₀]; exact (hd0₁ r).ge)
      (by rw [hhost₀ r, hsend₀]; exact (hd0₂ r).le)
      (by rw [hhost₀ r, hsend₀]; exact (hd0₁ r).le)
      (by simpa [IdealConstantWorld.toBounds] using hslew0) hslew1
      (by
        rw [latencyError_ideal, hpl]
        have hrate : w₀.rate = m.rate := hw.rate_eq
        simp only [IdealConstantWorld.toBounds, hm₀, IdealConstantWorld.starShifted, hrate]
        simpa using hlat r)
    rw [latencyError_ideal] at h
    exact h
  choose K hK using hspeaker
  -- The baseline plays the same in the given world.
  have hstar : σ.IsStar w.sender := by
    have h := fixedDelay_isStar (R := R) p
    rw [hps, ← hw.sender_eq] at h
    exact h
  have hprog : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n :=
    progress p w m.toBounds hwb lookahead
  have hprog₀ : ∀ T : Time, ∃ n, T < σ.eventTime w₀ lookahead n :=
    progress p w₀ m₀.toBounds hwb₀ lookahead
  have hplays : σ.plays w₀ lookahead = σ.plays w lookahead :=
    σ.plays_shiftStarKeepPeers w lookahead hstar (-Δ) (by rw [hw.sender_eq]; simp [hΔs])
      (hw.starNet hxneg) hprog hprog₀ hcoll
  -- So each speaker plays every output sample late by its host's asymmetry.
  have hKw : w.PlaysAtLatencies (σ.plays w lookahead)
      (fun r => p.latency + m.asymmetry (m.host r)) (Finset.univ.sup K) := by
    intro r k hk
    obtain ⟨hcont, x, hx, hE⟩ :=
      hK r k (le_trans (Finset.le_sup (Finset.mem_univ r)) hk)
    rw [hplays] at hcont hx
    refine ⟨hcont, x, hx, ?_⟩
    have hout : (w₀.speaker r).out k = (w.speaker r).out k + (-Δ) (w.host r) := rfl
    have hcap : w₀.captured x = w.captured x := rfl
    have hhr : w.host r = m.host r := by rw [hw.host_eq]
    have h0 := abs_nonpos_iff.mp hE
    rw [hout, hcap, hhr, Pi.neg_apply, hΔh _ (hnos r)] at h0
    linarith
  exact ⟨_, hKw⟩

/-- **The baseline's cost in an ideal constant world.** Consider an ideal
constant world in which no speaker is on the sender's host. Let the baseline
send the stream to every speaker's host and play at the target latency, with
at least one copy of each message and a slew between zero and one. Let the
target latency exceed, for every speaker, the delivery margin: the spans of
the resampler's lookahead and of two blocks, half the round trip between the
sender and the speaker's host, and the request lead. Suppose that no two
messages from different hosts arrive at one host at the same time. When the
weights of latency and of roughness are zero, the baseline's cost is at most

* the weight of synchronization times the sum, over the pairs of speakers,
  of the squares of the differences of their hosts' asymmetries, divided by
  the square of the number of speakers, plus
* the weight of tracking times the mean, over the speakers, of the square of
  the host's asymmetry. -/
theorem cost_le_of_ideal (m : IdealConstantWorld H R) (w : World H R) (hw : m.Holds w)
    (hnos : ∀ r, m.host r ≠ m.sender) (lookahead : ℕ+) (c : Weights)
    (hcl : c.latency = 0) (hcr : c.roughness = 0)
    (hps : p.sender = m.sender) (hpr : p.rate = m.rate) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hnodup : p.speakers.Nodup) (hpl : p.latency = m.targetLatency) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hslew0 : 0 < p.slew) (hslew1 : p.slew < 1)
    (hlat : ∀ r, (((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate
      + (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2 + m.lead
        < m.targetLatency)
    (hcoll : (solution p : Solution H R Payload).NoCrossOriginCollision w lookahead) :
    (solution p : Solution H R Payload).cost w lookahead c
      ≤ c.sync * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
              ENNReal.ofReal ((m.asymmetry (m.host q.1) - m.asymmetry (m.host q.2)) ^ 2))
        + c.tracking
          * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (m.asymmetry (m.host r) ^ 2)) := by
  classical
  set σ : Solution H R Payload := solution p with hσ
  obtain ⟨K₀, hKw⟩ := playsAtLatencies_of_ideal p m w hw hnos lookahead hps hpr hpsp hnodup hpl
    hcopies hperiod hslew0 hslew1 hlat hcoll
  -- The cost of playing at exact latencies.
  obtain ⟨t₀, hcap⟩ := hw.captured_eq
  have htrack := w.tracking_le_of_exact (σ.plays w lookahead) hKw hcap hw.target_eq
  have hsync := w.sync_le_of_exact (σ.plays w lookahead) hKw hcap
  have hmiss := w.missed_eq_zero_of_exact (σ.plays w lookahead) hKw
  have hdisc := w.discontinuities_eq_zero_of_exact (σ.plays w lookahead) hKw
  have e1 : ∀ r, p.latency + m.asymmetry (m.host r) - m.targetLatency
      = m.asymmetry (m.host r) := fun r => by rw [hpl]; ring
  have e2 : ∀ q : Fin R × Fin R,
      p.latency + m.asymmetry (m.host q.1) - (p.latency + m.asymmetry (m.host q.2))
        = m.asymmetry (m.host q.1) - m.asymmetry (m.host q.2) := fun q => by ring
  simp only [e1] at htrack
  simp only [e2] at hsync
  have hcost := w.cost_le (σ.plays w lookahead) c
  rw [hmiss, hdisc, hcl, hcr] at hcost
  simp only [ENNReal.coe_zero, zero_mul, mul_zero, add_zero] at hcost
  calc σ.cost w lookahead c
      = w.cost (σ.plays w lookahead) c := rfl
    _ ≤ c.sync * w.sync (σ.plays w lookahead) + c.tracking * w.tracking (σ.plays w lookahead) :=
        hcost
    _ ≤ _ := by gcongr

/-- **The baseline plays every frame at a known time in an ideal constant
world.** Under the conditions of `playsAtLatencies_of_ideal`, from some
frame on every speaker plays every frame, exactly the target latency plus the
asymmetry of its host after the frame's capture. -/
theorem playTime_of_ideal (m : IdealConstantWorld H R) (w : World H R) (hw : m.Holds w)
    (hnos : ∀ r, m.host r ≠ m.sender) (lookahead : ℕ+)
    (hps : p.sender = m.sender) (hpr : p.rate = m.rate) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hnodup : p.speakers.Nodup) (hpl : p.latency = m.targetLatency) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hslew0 : 0 < p.slew) (hslew1 : p.slew < 1)
    (hlat : ∀ r, (((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate
      + (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2 + m.lead
        < m.targetLatency)
    (hcoll : (solution p : Solution H R Payload).NoCrossOriginCollision w lookahead) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ r,
      w.playTime ((solution p : Solution H R Payload).plays w lookahead) r n
        = some (w.source.capture n + (p.latency + m.asymmetry (m.host r))) := by
  obtain ⟨K, hK⟩ := playsAtLatencies_of_ideal p m w hw hnos lookahead hps hpr hpsp hnodup hpl
    hcopies hperiod hslew0 hslew1 hlat hcoll
  obtain ⟨t₀, hcap⟩ := hw.captured_eq
  exact hK.exists_playTime m.rate_pos hcap hw.out_unbounded

/-- **The baseline's exact cost in an ideal constant world.** Under the
conditions of `cost_le_of_ideal`, the baseline's cost is the shift cost of
the asymmetries of the speakers' hosts: the weight of synchronization times
their variance across the speakers, plus the weight of tracking times the
mean of their squares. -/
theorem cost_eq_of_ideal (m : IdealConstantWorld H R) (w : World H R) (hw : m.Holds w)
    (hnos : ∀ r, m.host r ≠ m.sender) (lookahead : ℕ+) (c : Weights)
    (hcl : c.latency = 0) (hcr : c.roughness = 0)
    (hps : p.sender = m.sender) (hpr : p.rate = m.rate) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hnodup : p.speakers.Nodup) (hpl : p.latency = m.targetLatency) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hslew0 : 0 < p.slew) (hslew1 : p.slew < 1)
    (hlat : ∀ r, (((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate
      + (m.delay m.sender (m.host r) + m.delay (m.host r) m.sender) / 2 + m.lead
        < m.targetLatency)
    (hcoll : (solution p : Solution H R Payload).NoCrossOriginCollision w lookahead)
    (hR : 0 < R) :
    (solution p : Solution H R Payload).cost w lookahead c
      = ENNReal.ofReal (shiftCost c fun r => m.asymmetry (m.host r)) := by
  refine le_antisymm ?_ ?_
  · rw [ofReal_shiftCost c hR]
    exact cost_le_of_ideal p m w hw hnos lookahead c hcl hcr hps hpr hpsp hnodup hpl hcopies
      hperiod hslew0 hslew1 hlat hcoll
  · obtain ⟨K, hK⟩ := playsAtLatencies_of_ideal p m w hw hnos lookahead hps hpr hpsp hnodup
      hpl hcopies hperiod hslew0 hslew1 hlat hcoll
    obtain ⟨t₀, hcap⟩ := hw.captured_eq
    have h := w.frameCost_le_cost_of_exact _ c hK m.rate_pos hcap hw.target_eq hw.out_unbounded
      hR hw.capture_unbounded
    rw [hpl, frameCost_const_add c hR] at h
    exact h

end Unisono.Solutions.FixedDelay
