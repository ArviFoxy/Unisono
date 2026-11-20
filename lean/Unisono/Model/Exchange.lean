/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Basic.Real.Basic

/-!
# An exchange of packets in both directions

Two hosts have clocks `cs` (the sender's) and `cr` (the receiver's), functions
of a true time that neither can read. A packet leaves the sender at true time
`a` and arrives at `a'`; a packet leaves the receiver at `b` and arrives at
`b'`. The four stamps are readings of the clock of the host where each event
happens. This file states what the stamps determine.
-/

@[expose] public noncomputable section

namespace Unisono.Model.Exchange

variable (cs cr : ℝ → ℝ) (a a' b b' : ℝ)

/-- The receiver's clock minus the sender's, at a true time. -/
def offset (t : ℝ) : ℝ := cr t - cs t

/-- Transit time of the packet from the sender, read on the sender's clock. -/
def delayOut : ℝ := cs a' - cs a

/-- Transit time of the packet to the sender, read on the sender's clock. -/
def delayBack : ℝ := cs b' - cs b

/-- Half the difference of the two apparent transit times: the estimate of the offset. -/
def offsetEstimate : ℝ := ((cr a' - cs a) - (cs b' - cr b)) / 2

/-- The time the sender waited, less the time the receiver held the exchange. -/
def roundTrip : ℝ := (cs b' - cs a) - (cr b - cr a')

/-- The estimate is the mean of the offsets at the receiver's two events, plus
half the difference of the delays. -/
theorem offset_identity :
    offsetEstimate cs cr a a' b b'
      = (offset cs cr a' + offset cs cr b) / 2
        + (delayOut cs a a' - delayBack cs b b') / 2 := by
  simp only [offsetEstimate, offset, delayOut, delayBack]
  ring

/-- The round trip is the sum of the delays, less the change of the offset
while the receiver held the exchange. -/
theorem round_trip_identity :
    roundTrip cs cr a a' b b'
      = delayOut cs a a' + delayBack cs b b'
        - (offset cs cr b - offset cs cr a') := by
  simp only [roundTrip, offset, delayOut, delayBack]
  ring

/-- If each delay is at least the smallest delay of its direction (`δout`,
`δback`), the estimate differs from the mean offset plus half the difference
of the smallest delays by at most half the excess of the two delays. The
constant `(δout - δback) / 2` is what no exchange reveals. -/
theorem error_bound (δout δback : ℝ)
    (hout : δout ≤ delayOut cs a a') (hback : δback ≤ delayBack cs b b') :
    |offsetEstimate cs cr a a' b b'
        - (offset cs cr a' + offset cs cr b) / 2 - (δout - δback) / 2|
      ≤ (delayOut cs a a' + delayBack cs b b' - (δout + δback)) / 2 := by
  rw [offset_identity, abs_le]
  constructor <;> linarith

end Unisono.Model.Exchange
