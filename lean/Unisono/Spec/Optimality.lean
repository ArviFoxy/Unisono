/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives

/-!
# Optimality in expected cost

What it means for a solution to be optimal when the world is random.

A solution is judged by its expected cost (`Solution.expectedCost`): the mean
of the cost of its playback over the worlds that a probability measure draws.
A solution is optimal when no other solution has a lower expected cost. The
comparison is between means: in one world a solution with a larger expected
cost can still cost less, as a decision that is right on average can still
turn out badly.

* A **random world** is a probability measure `P` on a space `Ω` together
  with a map `world : Ω → World H R`. A **set of random worlds**
  (`RandomWorlds`) says which of them are considered.
* A model is a **family** of such sets, one for each value of an index
  `f : ι`. The index holds whatever a solution is not told and the model does
  not draw at random: numbers that a solution has to measure for itself.
* A **class of solutions** (`SolutionClass`) says which solutions are
  compared, whatever messages they exchange. `allSolutions` compares all of
  them.
* `OptimalWithin` says that the expected cost of one solution `σ` exceeds
  that of no allowed solution by more than a margin, in every random world of
  every member of the family. The margin `ε f` may depend on the member,
  because a cost in seconds squared cannot have one margin for networks of
  all sizes.

The weights `c` of the objectives and the lookahead come first: a solution
is designed for them and may depend on them, and a statement of optimality
is about one choice of them. A family of solutions, one for each choice of
weights, is optimal when each of its solutions is optimal for its weights.

In `OptimalWithin` the solution `σ` is fixed before the member `f` and the
random world are chosen, so it cannot depend on them: it uses only what the
model tells every solution. The solution `τ` that it is compared with is
chosen afterwards, so `τ` may be designed for that one member. A solution
that is optimal in this sense does as well as one that is told the index.

That is possible only for an index that a solution can learn from what it
observes. Whatever cannot be learned has to be drawn at random inside each
member, with a stated law; otherwise a solution designed for one member wins
there and no solution is optimal.

The expected cost is a lower integral. When the cost of a solution is not a
measurable function of the outcome, its lower integral can lie below its cost
in almost every outcome, so such a solution can appear better than every
solution whose cost is measurable. A statement of optimality therefore has
to restrict the class of solutions to those whose cost is a measurable
function of what is drawn. For the generative world that class is
`GenerativeWorld.measurableCost`.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory
open scoped ENNReal

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- A set of random worlds: for each probability space, which measures and
which maps to worlds belong to it. -/
abbrev RandomWorlds (H : Type) (R : ℕ) : Type 1 :=
  ∀ (Ω : Type) [MeasurableSpace Ω], Measure Ω → (Ω → World H R) → Prop

/-- A class of solutions: for each type of message, which solutions belong. -/
abbrev SolutionClass (H : Type) (R : ℕ) : Type 1 :=
  ∀ (Msg : Type), Solution H R Msg → Prop

/-- The class of all solutions. -/
def allSolutions : SolutionClass H R := fun _ _ => True

/-- The solution `σ` is allowed, and in every random world of every member
`f` of the family `laws` its expected cost exceeds that of no allowed
solution by more than `ε f`, for a resampler lookahead of `lookahead` frames
and weights `c`. With `ε = 0` no allowed solution does better. -/
def OptimalWithin {ι : Type} (laws : ι → RandomWorlds H R) (allowed : SolutionClass H R)
    (lookahead : ℕ+) (c : Weights) (ε : ι → ℝ≥0∞) (σ : Solution H R Msg) : Prop :=
  allowed Msg σ ∧
    ∀ (f : ι) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (world : Ω → World H R),
      laws f Ω P world → ∀ (Msg' : Type) (τ : Solution H R Msg'), allowed Msg' τ →
        σ.expectedCost P world lookahead c ≤ τ.expectedCost P world lookahead c + ε f

/-- **The least expected cost is one number.** Two solutions that are both
optimal with no margin have the same expected cost in every random world of
every member. -/
theorem OptimalWithin.expectedCost_eq {ι : Type} {laws : ι → RandomWorlds H R}
    {allowed : SolutionClass H R} {lookahead : ℕ+} {c : Weights}
    {σ : Solution H R Msg} {Msg' : Type} {τ : Solution H R Msg'}
    (hσ : OptimalWithin laws allowed lookahead c 0 σ)
    (hτ : OptimalWithin laws allowed lookahead c 0 τ)
    {f : ι} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {world : Ω → World H R}
    (h : laws f Ω P world) :
    σ.expectedCost P world lookahead c = τ.expectedCost P world lookahead c := by
  refine le_antisymm ?_ ?_
  · simpa using hσ.2 f Ω P world h Msg' τ hτ.1
  · simpa using hτ.2 f Ω P world h Msg σ hσ.1

end Unisono.Spec
