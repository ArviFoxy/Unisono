/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Fixed
public import Unisono.Scalar

/-!
# The sender of a stream

What the functions of `unisono_core::sender` do to the numbering of frames,
the level ramp carried in packet headers, and the departure stamp.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Sender

/-- The departure that a sender knows is of a packet that it sent in this
timeline: the first frame of that packet is before the next frame. -/
def Stamped (s : sender.Sender) : Prop :=
  s.stamped = true → s.stamped_index.val < s.next.val

/-- The level ramp is anchored at or before the next frame to send. -/
def Anchored (s : sender.Sender) : Prop :=
  s.level_index.val ≤ s.next.val

/-- The latency carried by the next packet, as an integer in nanoseconds,
obtained by advancing `level_base` along `level_slope` from `level_index`
to `next` and saturating to signed 64 bits. -/
def levelAt (s : sender.Sender) : ℤ :=
  let elapsed : ℤ := ((s.next.val - s.level_index.val : ℕ) : ℤ)
  let delta : ℤ :=
    if s.settings.rate.val = 0 then 0
    else (elapsed * s.level_slope.val) / (s.settings.rate.val : ℤ)
  Fixed.clamp64 (s.level_base.val + delta)

private theorem prod_95_bounds (a b : ℤ)
    (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 64)
    (hb0 : -2 ^ 31 ≤ b) (hb1 : b < 2 ^ 31) :
    -2 ^ 95 ≤ a * b ∧ a * b < 2 ^ 95 := by
  constructor <;> nlinarith

private theorem ediv_95_bounds (a b : ℤ) (hb : 0 < b)
    (ha0 : -2 ^ 95 ≤ a) (ha1 : a < 2 ^ 95) :
    -2 ^ 95 ≤ a / b ∧ a / b ≤ 2 ^ 95 := by
  constructor
  · rw [Int.le_ediv_iff_mul_le hb]
    have hmul : -2 ^ 95 * b ≤ -2 ^ 95 := by nlinarith
    omega
  · have hlt : a / b < 2 ^ 95 + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hb]
      have hmul : 2 ^ 95 ≤ (2 ^ 95 + 1) * b := by nlinarith
      omega
    omega

/-- `current_level` never overflows and equals `levelAt s`. -/
@[step]
theorem current_level_spec (s : sender.Sender) :
    sender.Sender.current_level s ⦃ r => r.val = levelAt s ⦄ := by
  unfold sender.Sender.current_level
  step as ⟨elapsed, helapsed⟩
  have hel_val : elapsed.val = s.next.val - s.level_index.val := by
    rw [helapsed, U64.saturating_sub_val]
  step as ⟨i, hi⟩
  have hi_val : i.val = (elapsed.val : ℤ) := by
    rw [hi, U64.hcast_I128_val]
  step as ⟨i1, hi1⟩
  have hi1_val : i1.val = s.level_slope.val := by
    rw [hi1, I32.cast_I128_val]
  have hel_lt : (elapsed.val : ℤ) < 2 ^ 64 := by
    scalar_tac
  have hslope_bounds : -2 ^ 31 ≤ s.level_slope.val ∧ s.level_slope.val < 2 ^ 31 := by
    scalar_tac
  have hprod_bounds : -2 ^ 95 ≤ i.val * i1.val ∧ i.val * i1.val < 2 ^ 95 := by
    rw [hi_val, hi1_val]
    exact prod_95_bounds _ _ (by omega) hel_lt hslope_bounds.1 hslope_bounds.2
  step as ⟨i2, hi2⟩
  have hi2_val : i2.val = i.val * i1.val := by
    rw [hi2, I128.wrapping_mul_val _ _ (by omega)]
  step as ⟨i3, hi3⟩
  have hi3_val : i3.val = (s.settings.rate.val : ℤ) := by
    rw [hi3, U32.hcast_I64_val]
  step with Fixed.div_floor_spec as ⟨delta, hdelta_pos, hdelta_nonpos⟩
  have hdelta_val :
      delta.val =
        if s.settings.rate.val = 0 then 0
        else (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
          (s.settings.rate.val : ℤ) := by
    by_cases hrate : s.settings.rate.val = 0
    · simp only [hrate, ↓reduceIte]
      exact hdelta_nonpos (by omega)
    · simp only [hrate, ↓reduceIte]
      have hpos : 0 < i3.val := by omega
      rw [hdelta_pos hpos, hi2_val, hi_val, hi1_val, hi3_val, hel_val]
  have hdelta_bounds : -2 ^ 95 ≤ delta.val ∧ delta.val ≤ 2 ^ 95 := by
    by_cases hrate : s.settings.rate.val = 0
    · have h0 : delta.val = 0 := hdelta_nonpos (by omega)
      omega
    · have hpos : 0 < i3.val := by omega
      rw [hdelta_pos hpos, hi2_val]
      exact ediv_95_bounds _ _ hpos hprod_bounds.1 hprod_bounds.2
  step as ⟨i4, hi4⟩
  have hi4_val : i4.val = s.level_base.val := by
    rw [hi4, I64.cast_I128_val]
  have hbase_bounds : -2 ^ 63 ≤ s.level_base.val ∧ s.level_base.val < 2 ^ 63 := by
    scalar_tac
  step as ⟨i5, hi5⟩
  have hi5_val : i5.val = i4.val + delta.val := by
    rw [hi5, I128.wrapping_add_val _ _ (by omega)]
  step with Fixed.saturate_spec as ⟨r, hr⟩
  rw [hr, hi5_val, hi4_val, hdelta_val]
  rfl

/-- When the sample rate is positive and the ramped value stays within signed
64-bit range, `levelAt s` is the exact floor of the rational ramp from
`level_index` to `next`, with no cumulative rounding drift. -/
theorem levelAt_eq_floor (s : sender.Sender)
    (hrate : 0 < s.settings.rate.val)
    (hlo : -2 ^ 63 ≤ s.level_base.val +
      (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
        (s.settings.rate.val : ℤ))
    (hhi : s.level_base.val +
      (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
        (s.settings.rate.val : ℤ) ≤ 2 ^ 63 - 1) :
    levelAt s =
      ⌊(s.level_base.val : ℚ) +
        (((s.next.val - s.level_index.val : ℕ) : ℚ) * (s.level_slope.val : ℚ)) /
          (s.settings.rate.val : ℚ)⌋ := by
  have hne : s.settings.rate.val ≠ 0 := by omega
  unfold levelAt Fixed.clamp64
  simp only [hne, ↓reduceIte]
  have hclamp :
      max (-2 ^ 63)
        (min (s.level_base.val +
          (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
            (s.settings.rate.val : ℤ)) (2 ^ 63 - 1)) =
      s.level_base.val +
        (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
          (s.settings.rate.val : ℤ) := by
    omega
  rw [hclamp, Int.floor_intCast_add]
  have hdiv :
      (((s.next.val - s.level_index.val : ℕ) : ℚ) * (s.level_slope.val : ℚ)) /
        (s.settings.rate.val : ℚ) =
      (((((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val : ℤ)) : ℚ) /
        ((s.settings.rate.val : ℕ) : ℚ) := by
    push_cast
    rfl
  rw [hdiv, Rat.floor_intCast_div_natCast]

/-- Setting the level anchors the ramp at `next` and immediately takes effect
for the next packet. -/
theorem level_spec (s : sender.Sender) (level : Std.I64) (slope : Std.I32) :
    sender.Sender.level s level slope ⦃ s' =>
      s'.timeline = s.timeline ∧ s'.next = s.next
      ∧ s'.level_index = s.next ∧ s'.level_base = level ∧ s'.level_slope = slope
      ∧ Anchored s' ∧ levelAt s' = level.val
      ∧ (Stamped s → Stamped s') ⦄ := by
  unfold sender.Sender.level
  rw [WP.spec_ok]
  have hbounds : -2 ^ 63 ≤ level.val ∧ level.val ≤ 2 ^ 63 - 1 := by scalar_tac
  refine ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, ?_, fun h => h⟩
  unfold levelAt Fixed.clamp64
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, Int.zero_ediv, ite_self, add_zero]
  omega

/-- The header of the next packet. Its first frame is the next frame of the
timeline, its level equals `levelAt s`, its slope is `s.level_slope`, and the
frame after its last is the next frame afterwards, so the packets of a timeline
follow each other without a break. The numbering stops at the largest index. A
header that says it carries a departure carries that of a packet whose first
frame is before its own. -/
theorem packet_spec (s : sender.Sender) (frames : Std.U16) (capture : Std.I64)
    (drift : Std.I32) :
    sender.Sender.packet s frames capture drift ⦃ out =>
      out.1.timeline = s.timeline ∧ out.1.index = s.next ∧ out.1.frames = frames
      ∧ out.1.capture = capture ∧ out.1.drift = drift
      ∧ out.1.level.val = levelAt s ∧ out.1.level_slope = s.level_slope
      ∧ out.2.timeline = s.timeline
      ∧ out.2.next.val = min U64.max (s.next.val + frames.val)
      ∧ out.2.settings = s.settings
      ∧ out.2.level_index = s.level_index
      ∧ out.2.level_base = s.level_base
      ∧ out.2.level_slope = s.level_slope
      ∧ (Anchored s → Anchored out.2)
      ∧ (Stamped s → Stamped out.2)
      ∧ (out.1.flags = packet.FLAG_STAMPED ↔ s.stamped = true)
      ∧ (Stamped s → s.stamped = true → out.1.stamped_index.val < out.1.index.val) ⦄ := by
  unfold sender.Sender.packet
  step with current_level_spec as ⟨lvl, hlvl⟩
  step as ⟨i, hi⟩
  have hiv : i.val = frames.val := by
    rw [hi, UScalar.cast_val_mod_pow_of_inBounds_eq]
    scalar_tac
  step as ⟨next, hnext⟩
  have hnv : next.val = min U64.max (s.next.val + frames.val) := by
    rw [hnext, U64.saturating_add_val, hiv]
  have hmax : s.next.val ≤ U64.max := by scalar_tac
  have hflag : (0#u16 : Std.U16) ≠ packet.FLAG_STAMPED := by
    simp [packet.FLAG_STAMPED]
  split
  · rename_i hst
    rw [WP.spec_ok]
    dsimp only
    refine ⟨rfl, rfl, rfl, rfl, rfl, hlvl, rfl, rfl, hnv, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro hA
      change s.level_index.val ≤ s.next.val at hA
      change s.level_index.val ≤ next.val
      omega
    · intro hS hst'
      have := hS hst'
      change s.stamped_index.val < next.val
      omega
    · simp [hst]
    · intro hS _
      exact hS hst
  · rename_i hst
    have hst' : s.stamped = false := by simpa using hst
    rw [WP.spec_ok]
    dsimp only
    refine ⟨rfl, rfl, rfl, rfl, rfl, hlvl, rfl, rfl, hnv, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro hA
      change s.level_index.val ≤ s.next.val at hA
      change s.level_index.val ≤ next.val
      omega
    · intro _ hc
      change s.stamped = true at hc
      rw [hst'] at hc
      cases hc
    · simp [hst', hflag]
    · intro _ hc
      rw [hst'] at hc
      cases hc

/-- Two consecutive packets on a ramp advance `level` by the exact rational
increment `frames * slope / rate`, to within strictly less than 1 ns. -/
theorem packet_ramp_consistent (s : sender.Sender) (frames1 frames2 : Std.U16)
    (capture1 capture2 : Std.I64) (drift1 drift2 : Std.I32)
    (hA : Anchored s)
    (hrate : 0 < s.settings.rate.val)
    (hfit : s.next.val + frames1.val ≤ U64.max)
    (hlo1 : -2 ^ 63 ≤ s.level_base.val +
      (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
        (s.settings.rate.val : ℤ))
    (hhi1 : s.level_base.val +
      (((s.next.val - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
        (s.settings.rate.val : ℤ) ≤ 2 ^ 63 - 1)
    (hlo2 : -2 ^ 63 ≤ s.level_base.val +
      ((((s.next.val + frames1.val) - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
        (s.settings.rate.val : ℤ))
    (hhi2 : s.level_base.val +
      ((((s.next.val + frames1.val) - s.level_index.val : ℕ) : ℤ) * s.level_slope.val) /
        (s.settings.rate.val : ℤ) ≤ 2 ^ 63 - 1) :
    (do
      let p1 ← sender.Sender.packet s frames1 capture1 drift1
      let p2 ← sender.Sender.packet p1.2 frames2 capture2 drift2
      ok (p1.1, p2.1))
    ⦃ out =>
      out.1.level_slope = out.2.level_slope
      ∧ |((out.2.level.val - out.1.level.val : ℤ) : ℚ) -
          (frames1.val : ℚ) * (s.level_slope.val : ℚ) / (s.settings.rate.val : ℚ)| < 1 ⦄ := by
  step with packet_spec s frames1 capture1 drift1 as
    ⟨p1, _, _, _, _, _, hl1, hsl1, _, hnext1, hset1, hli1, hlb1, hls1, _, _, _, _⟩
  step with packet_spec p1.2 frames2 capture2 drift2 as
    ⟨p2, _, _, _, _, _, hl2, hsl2, _, _, _, _, _, _, _, _, _, _⟩
  refine ⟨by rw [hsl1, hsl2, hls1], ?_⟩
  have hnext1_eq : p1.2.next.val = s.next.val + frames1.val := by
    rw [hnext1, min_eq_right hfit]
  have hfl1 := levelAt_eq_floor s hrate hlo1 hhi1
  have hfl2 : levelAt p1.2 =
      ⌊(s.level_base.val : ℚ) +
        ((((s.next.val + frames1.val) - s.level_index.val : ℕ) : ℚ) * (s.level_slope.val : ℚ)) /
          (s.settings.rate.val : ℚ)⌋ := by
    have h := levelAt_eq_floor p1.2 (by rw [hset1]; exact hrate)
      (by rw [hset1, hlb1, hli1, hls1, hnext1_eq]; exact hlo2)
      (by rw [hset1, hlb1, hli1, hls1, hnext1_eq]; exact hhi2)
    simpa [hset1, hlb1, hli1, hls1, hnext1_eq] using h
  set q1 : ℚ := (s.level_base.val : ℚ) +
    (((s.next.val - s.level_index.val : ℕ) : ℚ) * (s.level_slope.val : ℚ)) /
      (s.settings.rate.val : ℚ)
  set q2 : ℚ := (s.level_base.val : ℚ) +
    ((((s.next.val + frames1.val) - s.level_index.val : ℕ) : ℚ) * (s.level_slope.val : ℚ)) /
      (s.settings.rate.val : ℚ)
  have hdiff_q : q2 - q1 =
      (frames1.val : ℚ) * (s.level_slope.val : ℚ) / (s.settings.rate.val : ℚ) := by
    have hnat : (s.next.val + frames1.val) - s.level_index.val =
        (s.next.val - s.level_index.val) + frames1.val := by
      change s.level_index.val ≤ s.next.val at hA
      omega
    dsimp only [q1, q2]
    rw [hnat]
    push_cast
    ring
  have hle1 : (⌊q1⌋ : ℚ) ≤ q1 := Int.floor_le q1
  have hlt1 : q1 < (⌊q1⌋ : ℚ) + 1 := Int.lt_floor_add_one q1
  have hle2 : (⌊q2⌋ : ℚ) ≤ q2 := Int.floor_le q2
  have hlt2 : q2 < (⌊q2⌋ : ℚ) + 1 := Int.lt_floor_add_one q2
  rw [hl1, hl2, hfl1, hfl2]
  push_cast
  rw [← hdiff_q, abs_lt]
  constructor <;> linarith

/-- Taking in a departure keeps the known departure one of a packet that was
sent in this timeline, and changes neither the timeline nor the numbering nor
the level ramp. -/
theorem departed_spec (s : sender.Sender) (timeline index : Std.U64) (departure : Std.I64) :
    sender.Sender.departed s timeline index departure ⦃ s' =>
      s'.timeline = s.timeline ∧ s'.next = s.next
      ∧ s'.level_index = s.level_index ∧ s'.level_base = s.level_base
      ∧ s'.level_slope = s.level_slope
      ∧ (Anchored s → Anchored s')
      ∧ (Stamped s → Stamped s') ⦄ := by
  unfold sender.Sender.departed
  split
  · simp
  · split
    · simp
    · rename_i hlt
      have hlt' : index.val < s.next.val := by scalar_tac
      split
      · split
        · simp
        · rw [WP.spec_ok]
          refine ⟨rfl, rfl, rfl, rfl, rfl, fun h => h, fun _ _ => hlt'⟩
      · rw [WP.spec_ok]
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun h => h, fun _ _ => hlt'⟩

/-- A restart starts a timeline with a larger number, unless the number was
the largest there is, and numbers its frames from zero. No departure of the
new timeline is known. The current ramped level and slope are preserved,
re-anchored at frame 0. -/
theorem restart_spec (s : sender.Sender) (timeline : Std.U64) :
    sender.Sender.restart s timeline ⦃ s' =>
      s'.next.val = 0 ∧ s'.stamped = false
      ∧ s'.level_index.val = 0 ∧ s'.level_base.val = levelAt s
      ∧ s'.level_slope = s.level_slope ∧ Anchored s' ∧ levelAt s' = levelAt s
      ∧ s.timeline.val ≤ s'.timeline.val ∧ timeline.val ≤ s'.timeline.val
      ∧ (s.timeline.val < U64.max → s.timeline.val < s'.timeline.val) ⦄ := by
  unfold sender.Sender.restart
  step with current_level_spec as ⟨lvl, hlvl⟩
  have hlvl_bounds : -2 ^ 63 ≤ lvl.val ∧ lvl.val ≤ 2 ^ 63 - 1 := by scalar_tac
  step as ⟨after, hafter⟩
  have hav : after.val = min U64.max (s.timeline.val + 1) := by
    rw [hafter, U64.saturating_add_val]
    rfl
  have hmax : s.timeline.val ≤ U64.max := by scalar_tac
  have hlevel_zero :
      ∀ (tl : Std.U64),
        levelAt { s with timeline := tl, next := 0#u64, level_index := 0#u64,
                         level_base := lvl, stamped := false } = levelAt s := by
    intro tl
    rw [← hlvl]
    unfold levelAt Fixed.clamp64
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, Int.zero_ediv, ite_self, add_zero]
    omega
  split
  · rename_i hgt
    have : after.val < timeline.val := by scalar_tac
    rw [WP.spec_ok]
    dsimp only
    refine ⟨rfl, rfl, rfl, hlvl, rfl, le_refl _, hlevel_zero timeline, ?_, le_refl _, fun _ => ?_⟩
      <;> omega
  · rename_i hle
    have : timeline.val ≤ after.val := by scalar_tac
    rw [WP.spec_ok]
    dsimp only
    refine ⟨rfl, rfl, rfl, hlvl, rfl, le_refl _, hlevel_zero after, ?_, ?_, fun _ => ?_⟩
      <;> omega

/-- The answer to a report of the sender's stream names the receiver and the
number of the report and gives the times at which the report arrived and the
echo left. A report of another stream gets no answer. -/
theorem answer_spec (s : sender.Sender) (report : packet.Report) (arrival departure : Std.I64) :
    sender.Sender.answer s report arrival departure ⦃ out =>
      (report.stream ≠ s.settings.stream → out = none)
      ∧ (report.stream = s.settings.stream →
          out = some ⟨report.stream, report.receiver, report.sequence, arrival, departure⟩) ⦄ := by
  unfold sender.Sender.answer
  split
  · rename_i h
    have hne : report.stream ≠ s.settings.stream := by simpa using h
    simp [hne]
  · rename_i h
    have heq : report.stream = s.settings.stream := by
      have : ¬ report.stream ≠ s.settings.stream := by simpa using h
      exact not_not.mp this
    simp [heq]

end Unisono.Sender
