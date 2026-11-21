/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The best law for a receiver's pace

A receiver reads the stream once in each cycle of its device. Before a cycle
it knows two numbers:

* `E`, the distance by which the position it reads at is behind the schedule,
  in frames;
* `v`, how many frames more than the schedule advances its last cycle read:
  the pace it has, measured against the pace of the schedule.

It then chooses `w`, the change of its pace for this cycle. The cycle reads
`v + w` frames more than the schedule advances, so the distance after it is
`E - v - w`. Between two cycles the receiver's estimate of the schedule is
revised: its position by `ξ.1` frames and its pace by `-ξ.2` frames a cycle.
One cycle therefore takes the state `(E, v)` to

    (E - v - w + ξ.1,  v + w + ξ.2).

A cycle costs `ρ E² + w²`: the squared distance to the schedule, weighted by
`ρ`, and the squared change of the pace, which is what is heard as a change
of pitch. The problem is to choose every `w` from what is known before its
cycle so that the cost of all cycles is as small as possible.

This file solves the problem without revisions (`ξ = 0`), for every starting
state. The laws that are best form a family with one parameter `g`, strictly
between 0 and 1:

    w = g² / (2 - g) · E  -  g · v,

and the member `g` is best for the weight `ρ = g⁴ / ((2 - g)² (1 - g))`,
which takes every positive value once. The cost of all cycles from a state
`x` under this law is `value g x`, and no sequence of changes of the pace
costs less (`total_cost_ge`, `total_cost_law`). The proof is one identity
(`cost_add_value`): the cost of a cycle plus the value after it is the value
before it plus a multiple of the squared distance of `w` from the law.

The same identity gives the statement with revisions that cannot be foreseen,
in `Unisono.Model.RegulationRandom`.
-/

@[expose] public noncomputable section

namespace Unisono.Model.Regulation

open Filter Topology

/-- The gain on the distance that goes with the gain `g` on the pace. -/
def gainE (g : ℝ) : ℝ := g ^ 2 / (2 - g)

/-- The weight of the squared distance, against a weight of one on the
squared change of the pace, for which the law with gain `g` is the best. -/
def weight (g : ℝ) : ℝ := g ^ 4 / ((2 - g) ^ 2 * (1 - g))

/-- The cost of a cycle that starts in state `x` and changes the pace by `w`. -/
def cost (g : ℝ) (x : ℝ × ℝ) (w : ℝ) : ℝ := weight g * x.1 ^ 2 + w ^ 2

/-- The state after a cycle that starts in state `x`, changes the pace by `w`,
and after which the schedule is revised by `ξ`. -/
def next (x : ℝ × ℝ) (w : ℝ) (ξ : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - x.2 - w + ξ.1, x.2 + w + ξ.2)

/-- The law: the change of the pace in state `x`. -/
def law (g : ℝ) (x : ℝ × ℝ) : ℝ := gainE g * x.1 - g * x.2

/-- The cost of all cycles from state `x` under the law, as `total_cost_law`
shows. -/
def value (g : ℝ) (x : ℝ × ℝ) : ℝ :=
  g ^ 3 / ((2 - g) * (1 - g)) * x.1 ^ 2 - 2 * gainE g * x.1 * x.2 + g * x.2 ^ 2

/-- The bilinear form of which `value` is the square. -/
def pairing (g : ℝ) (x y : ℝ × ℝ) : ℝ :=
  g ^ 3 / ((2 - g) * (1 - g)) * x.1 * y.1 - gainE g * (x.1 * y.2 + x.2 * y.1) + g * x.2 * y.2

/-- One cycle under the law, without a revision. -/
def step (g : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := next x (law g x) 0

theorem weight_pos {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) : 0 < weight g := by
  have h1 : 0 < 1 - g := by linarith
  have h2 : 0 < 2 - g := by linarith
  unfold weight
  positivity

/-- The value is a sum of two squares: of the distance, and of how far the
pace is from the pace that the law holds at that distance. -/
theorem value_eq_squares {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) :
    value g x = g * (x.2 - g / (2 - g) * x.1) ^ 2 + weight g / g * x.1 ^ 2 := by
  have h1 : 1 - g ≠ 0 := by linarith
  have h2 : 2 - g ≠ 0 := by linarith
  have h0 : g ≠ 0 := hg0.ne'
  simp only [value, weight, gainE]
  field_simp
  ring

theorem value_nonneg {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) : 0 ≤ value g x := by
  rw [value_eq_squares hg0 hg1]
  have := weight_pos hg0 hg1
  positivity

/-- The value bounds the distance. -/
theorem distance_le_value {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) :
    weight g / g * x.1 ^ 2 ≤ value g x := by
  rw [value_eq_squares hg0 hg1]
  have : 0 ≤ g * (x.2 - g / (2 - g) * x.1) ^ 2 := by positivity
  linarith

/-- The value of a sum of two states. -/
theorem value_add (g : ℝ) (x y : ℝ × ℝ) :
    value g (x.1 + y.1, x.2 + y.2) = value g x + 2 * pairing g x y + value g y := by
  simp only [value, pairing]
  ring

/-- A revision of the schedule after a cycle adds to the value what it would
add to any state. -/
theorem value_next (g : ℝ) (x : ℝ × ℝ) (w : ℝ) (ξ : ℝ × ℝ) :
    value g (next x w ξ)
      = value g (next x w 0) + 2 * pairing g (next x w 0) ξ + value g ξ := by
  simp only [value, pairing, next, Prod.fst_zero, Prod.snd_zero]
  ring

/-- **The identity that everything rests on.** The cost of a cycle, plus the
value of the state after it, is the value of the state before it plus a
positive multiple of the squared distance between the change of the pace and
the law. -/
theorem cost_add_value {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) (w : ℝ) :
    cost g x w + value g (next x w 0) = value g x + (w - law g x) ^ 2 / (1 - g) := by
  have h1 : 1 - g ≠ 0 := by linarith
  have h2 : 2 - g ≠ 0 := by linarith
  simp only [cost, value, weight, gainE, next, law, Prod.fst_zero, Prod.snd_zero]
  field_simp
  ring

/-- Under the law a cycle costs the fraction `g` of the value. -/
theorem cost_law {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) :
    cost g x (law g x) = g * value g x := by
  have h1 : 1 - g ≠ 0 := by linarith
  have h2 : 2 - g ≠ 0 := by linarith
  simp only [cost, value, weight, gainE, law]
  field_simp
  ring

/-- Under the law a cycle multiplies the value by `1 - g`, exactly. -/
theorem value_step {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) :
    value g (step g x) = (1 - g) * value g x := by
  have h := cost_add_value hg0 hg1 x (law g x)
  rw [cost_law hg0 hg1] at h
  simp only [step]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero] at h
  linarith

/-- After `k` cycles under the law the value is `(1 - g)^k` times what it
was. -/
theorem value_iterate {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) (k : ℕ) :
    value g ((step g)^[k] x) = (1 - g) ^ k * value g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', value_step hg0 hg1, ih]
    ring

/-- From rest, where the pace is that of the schedule, as after a start or a
jump: the squared distance after `k` cycles under the law is at most
`(2 - g) (1 - g)^k` times the squared distance at the start. -/
theorem distance_from_rest {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (E : ℝ) (k : ℕ) :
    ((step g)^[k] (E, 0)).1 ^ 2 ≤ (2 - g) * (1 - g) ^ k * E ^ 2 := by
  have h1 : 0 < 1 - g := by linarith
  have h2 : 0 < 2 - g := by linarith
  have hw := weight_pos hg0 hg1
  have hd := distance_le_value hg0 hg1 ((step g)^[k] (E, 0))
  rw [value_iterate hg0 hg1] at hd
  have hrest : value g (E, 0) = g ^ 3 / ((2 - g) * (1 - g)) * E ^ 2 := by
    simp [value]
  rw [hrest] at hd
  -- multiply through by `g / weight g`, which is positive
  have hfac : weight g / g * ((2 - g) * (1 - g) ^ k * E ^ 2)
      = (1 - g) ^ k * (g ^ 3 / ((2 - g) * (1 - g)) * E ^ 2) := by
    simp only [weight]
    field_simp
  have hpos : 0 < weight g / g := by positivity
  have : weight g / g * ((step g)^[k] (E, 0)).1 ^ 2
      ≤ weight g / g * ((2 - g) * (1 - g) ^ k * E ^ 2) := by
    rw [hfac]
    exact hd
  exact le_of_mul_le_mul_left this hpos

/-! ## A schedule whose pace is wrong -/

/-- With a schedule that advances `d` frames more in each cycle than the
receiver is told, the law holds the state where the pace makes up for it and
the distance is `(2 - g) d / g`: that state is left as it is. -/
theorem step_with_pace_error {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (d : ℝ) :
    next ((2 - g) * d / g, d) (law g ((2 - g) * d / g, d)) (d, 0) = ((2 - g) * d / g, d) := by
  have h0 : g ≠ 0 := hg0.ne'
  have h2 : 2 - g ≠ 0 := by linarith
  have hlaw : law g ((2 - g) * d / g, d) = 0 := by
    simp only [law, gainE]
    field_simp
    ring
  simp only [next, hlaw, Prod.mk.injEq]
  constructor <;> ring

/-- Around that state the law moves the state as it does around the schedule
when the pace is right. -/
theorem next_shift {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (d : ℝ) (y : ℝ × ℝ) :
    next (y.1 + (2 - g) * d / g, y.2 + d) (law g (y.1 + (2 - g) * d / g, y.2 + d)) (d, 0)
      = ((step g y).1 + (2 - g) * d / g, (step g y).2 + d) := by
  have h0 : g ≠ 0 := hg0.ne'
  have h2 : 2 - g ≠ 0 := by linarith
  have hlaw : law g (y.1 + (2 - g) * d / g, y.2 + d) = law g y := by
    simp only [law, gainE]
    field_simp
    ring
  simp only [next, step, hlaw, Prod.fst_zero, Prod.snd_zero, Prod.mk.injEq]
  constructor <;> ring

/-! ## The limit of the pace -/

/-- One cycle under the law when the pace beyond the schedule is held within
`L` either way. -/
def stepLimited (g L : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - max (-L) (min L (x.2 + law g x)), max (-L) (min L (x.2 + law g x)))

/-- A cycle whose pace is held at the upper limit starts at least
`(2 - g) L / g` behind the schedule, and ends `L` nearer to it. So the limit
holds for no more cycles in a row than the distance holds limits. -/
theorem at_limit {g L : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hL : 0 < L) (x : ℝ × ℝ)
    (hv : x.2 ≤ L) (h : (stepLimited g L x).2 = L) :
    (2 - g) * L / g ≤ x.1 ∧ (stepLimited g L x).1 = x.1 - L := by
  have h2 : 0 < 2 - g := by linarith
  simp only [stepLimited] at h ⊢
  refine ⟨?_, by rw [h]⟩
  -- the pace that the law asks for is at least the limit
  have hfree : L ≤ x.2 + law g x := by
    by_contra hcon
    have hlt := lt_of_not_ge hcon
    rw [min_eq_right hlt.le] at h
    have : max (-L) (x.2 + law g x) < L := max_lt (by linarith) hlt
    linarith
  -- and the pace before it was at most the limit
  have hkeep : (1 - g) * x.2 ≤ (1 - g) * L := mul_le_mul_of_nonneg_left hv (by linarith)
  have hE : g * L ≤ gainE g * x.1 := by
    simp only [law] at hfree
    linarith
  rw [div_le_iff₀ hg0]
  have hgain : gainE g * x.1 * (2 - g) = g ^ 2 * x.1 := by
    simp only [gainE]
    field_simp
  nlinarith

/-! ## Every sequence of changes of the pace -/

/-- The states that the changes `w` of the pace lead through from `x`, when
the schedule is not revised. -/
def run (x : ℝ × ℝ) (w : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => x
  | k + 1 => next (run x w k) (w k) 0

/-- The cost of the first `n` cycles, plus the value of the state after them,
is the value at the start plus what each change of the pace differs from the
law by, squared and divided by `1 - g`. -/
theorem cost_sum {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) (w : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, cost g (run x w k) (w k)) + value g (run x w n)
      = value g x + ∑ k ∈ Finset.range n, (w k - law g (run x w k)) ^ 2 / (1 - g) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := cost_add_value hg0 hg1 (run x w n) (w n)
    have hrun : run x w (n + 1) = next (run x w n) (w n) 0 := rfl
    rw [hrun]
    linarith

/-- No `n` cycles cost less than the value at the start less the value after
them. -/
theorem cost_sum_ge {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) (w : ℕ → ℝ) (n : ℕ) :
    value g x - value g (run x w n) ≤ ∑ k ∈ Finset.range n, cost g (run x w k) (w k) := by
  have h := cost_sum hg0 hg1 x w n
  have h1 : 0 < 1 - g := by linarith
  have : 0 ≤ ∑ k ∈ Finset.range n, (w k - law g (run x w k)) ^ 2 / (1 - g) :=
    Finset.sum_nonneg fun k _ => by positivity
  linarith

/-- The changes of the pace that the law makes from `x`. -/
def lawful (g : ℝ) (x : ℝ × ℝ) (k : ℕ) : ℝ := law g ((step g)^[k] x)

theorem run_lawful (g : ℝ) (x : ℝ × ℝ) (k : ℕ) : run x (lawful g x) k = (step g)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change next (run x (lawful g x) k) (lawful g x k) 0 = step g ((step g)^[k] x)
    rw [ih]
    rfl

/-- Under the law the first `n` cycles cost the value at the start less the
value after them, which is `(1 - g)^n` times the value at the start. -/
theorem cost_sum_law {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, cost g (run x (lawful g x) k) (lawful g x k)
      = (1 - (1 - g) ^ n) * value g x := by
  have h := cost_sum hg0 hg1 x (lawful g x) n
  have hzero : ∑ k ∈ Finset.range n,
      (lawful g x k - law g (run x (lawful g x) k)) ^ 2 / (1 - g) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [run_lawful]
    simp [lawful]
  rw [hzero, run_lawful, value_iterate hg0 hg1] at h
  linarith

/-- **No sequence of changes of the pace costs less than the value.** If the
costs of all cycles add up at all, they add up to at least the value of the
state at the start. -/
theorem total_cost_ge {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) (w : ℕ → ℝ)
    (hs : Summable fun k => cost g (run x w k) (w k)) :
    value g x ≤ ∑' k, cost g (run x w k) (w k) := by
  have hw := weight_pos hg0 hg1
  set c : ℕ → ℝ := fun k => cost g (run x w k) (w k) with hc
  have hc0 : Tendsto c atTop (𝓝 0) := hs.tendsto_atTop_zero
  -- the distance and the change of the pace go to zero with the cost
  have hE2 : Tendsto (fun k => (run x w k).1 ^ 2) atTop (𝓝 0) := by
    have hbound : Tendsto (fun k => c k / weight g) atTop (𝓝 0) := by
      simpa using hc0.div_const (weight g)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun k => by positivity) (fun k => ?_)
    rw [le_div_iff₀ hw]
    have : 0 ≤ w k ^ 2 := by positivity
    simp only [hc, cost]
    linarith
  have hw2 : Tendsto (fun k => w k ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc0
      (fun k => by positivity) (fun k => ?_)
    have : 0 ≤ weight g * (run x w k).1 ^ 2 := by positivity
    simp only [hc, cost]
    linarith
  have root : ∀ f : ℕ → ℝ, Tendsto (fun k => f k ^ 2) atTop (𝓝 0) → Tendsto f atTop (𝓝 0) := by
    intro f hf
    have habs : Tendsto (fun k => |f k|) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hf
      rw [Real.sqrt_zero] at h
      exact h.congr fun k => Real.sqrt_sq_eq_abs (f k)
    exact (tendsto_zero_iff_abs_tendsto_zero f).mpr habs
  have hE : Tendsto (fun k => (run x w k).1) atTop (𝓝 0) := root _ hE2
  have hwz : Tendsto w atTop (𝓝 0) := root _ hw2
  -- so does the pace, which is what the distance changed by, less the change
  have hv : Tendsto (fun k => (run x w k).2) atTop (𝓝 0) := by
    have hE' : Tendsto (fun k => (run x w (k + 1)).1) atTop (𝓝 0) :=
      hE.comp (tendsto_add_atTop_nat 1)
    have : (fun k => (run x w k).2)
        = fun k => (run x w k).1 - (run x w (k + 1)).1 - w k := by
      funext k
      change (run x w k).2 = (run x w k).1 - (next (run x w k) (w k) 0).1 - w k
      simp only [next, Prod.fst_zero]
      ring
    rw [this]
    simpa using (hE.sub hE').sub hwz
  -- and with them the value
  have hval : Tendsto (fun k => value g (run x w k)) atTop (𝓝 0) := by
    have h1 := (hE.pow 2).const_mul (g ^ 3 / ((2 - g) * (1 - g)))
    have h2 := (hE.mul hv).const_mul (2 * gainE g)
    have h3 := (hv.pow 2).const_mul g
    have := (h1.sub h2).add h3
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      add_zero] at this
    refine this.congr fun k => ?_
    simp only [value]
    ring
  have hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, c k) atTop (𝓝 (∑' k, c k)) :=
    hs.hasSum.tendsto_sum_nat
  have hlow : Tendsto (fun n => value g x - value g (run x w n)) atTop (𝓝 (value g x)) := by
    simpa using tendsto_const_nhds.sub hval
  exact le_of_tendsto_of_tendsto' hlow hsum fun n => cost_sum_ge hg0 hg1 x w n

/-- **The law costs exactly the value.** The costs of all cycles under the law
add up to the value of the state at the start. -/
theorem total_cost_law {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (x : ℝ × ℝ) :
    HasSum (fun k => cost g (run x (lawful g x) k) (lawful g x k)) (value g x) := by
  have h1 : 0 ≤ 1 - g := by linarith
  have h2 : 1 - g < 1 := by linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hpow : Tendsto (fun n : ℕ => (1 - g) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one h1 h2
    have : Tendsto (fun n : ℕ => (1 - (1 - g) ^ n) * value g x) atTop (𝓝 (value g x)) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).mul_const (value g x)
      simp only [sub_zero, one_mul] at h
      exact h
    refine this.congr fun n => ?_
    rw [cost_sum_law hg0 hg1]
  · intro k
    have := weight_pos hg0 hg1
    simp only [cost]
    positivity

/-! ## The gain for given weights

The weight `ρ` of the squared distance is a number of the stream and of the
device: with a gain per second `κ`, the fourth root of the weight of the
timing error over the weight of the roughness, and cycles of length `h`, it
is `a⁴` for `a = κ h`. The law for it has `g = 1 - d²`, where `d`, strictly
between 0 and 1, is the smaller root of `d + 1/d = (a² + √(a⁴ + 16)) / 2`.
Then the gain on the distance is `a² d`, and a cycle multiplies the value by
`d²`. -/

/-- The sum of the modulus for `a` and its inverse. -/
def modulusSum (a : ℝ) : ℝ := (a ^ 2 + Real.sqrt (a ^ 4 + 16)) / 2

/-- The modulus for `a`: the square root of the factor by which the law for
the weight `a⁴` multiplies the value in each cycle. -/
def modulus (a : ℝ) : ℝ := (modulusSum a - Real.sqrt (modulusSum a ^ 2 - 4)) / 2

/-- The modulus lies strictly between 0 and 1, and `a² d (1 + d²) = (1 - d²)²`. -/
theorem modulus_spec {a : ℝ} (ha : 0 < a) :
    0 < modulus a ∧ modulus a < 1
      ∧ a ^ 2 * modulus a * (1 + modulus a ^ 2) = (1 - modulus a ^ 2) ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hR : Real.sqrt (a ^ 4 + 16) ^ 2 = a ^ 4 + 16 := Real.sq_sqrt (by positivity)
  have hR4 : 4 ≤ Real.sqrt (a ^ 4 + 16) := by
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h16]
    exact Real.sqrt_le_sqrt (by nlinarith [pow_pos ha 4])
  have hy : modulusSum a = (a ^ 2 + Real.sqrt (a ^ 4 + 16)) / 2 := rfl
  have hy2 : 2 < modulusSum a := by rw [hy]; linarith
  have hquad : modulusSum a ^ 2 - a ^ 2 * modulusSum a - 4 = 0 := by
    rw [hy]
    linear_combination (1 / 4 : ℝ) * hR
  have hs : Real.sqrt (modulusSum a ^ 2 - 4) ^ 2 = modulusSum a ^ 2 - 4 :=
    Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ Real.sqrt (modulusSum a ^ 2 - 4) := Real.sqrt_nonneg _
  have hsy : Real.sqrt (modulusSum a ^ 2 - 4) < modulusSum a := by nlinarith
  have hsy2 : modulusSum a - 2 < Real.sqrt (modulusSum a ^ 2 - 4) := by
    by_contra hcon
    have hle : Real.sqrt (modulusSum a ^ 2 - 4) ≤ modulusSum a - 2 := not_lt.mp hcon
    have : Real.sqrt (modulusSum a ^ 2 - 4) ^ 2 ≤ (modulusSum a - 2) ^ 2 := by nlinarith
    nlinarith
  have hd : modulus a ^ 2 - modulusSum a * modulus a + 1 = 0 := by
    simp only [modulus]
    linear_combination (1 / 4 : ℝ) * hs
  refine ⟨by simp only [modulus]; linarith, by simp only [modulus]; linarith, ?_⟩
  linear_combination (a ^ 2 * modulus a - (modulus a ^ 2 - modulusSum a * modulus a + 1)
    - 2 * modulusSum a * modulus a) * hd - modulus a ^ 2 * hquad

/-- The gain on the pace for `a`. -/
def gainFor (a : ℝ) : ℝ := 1 - modulus a ^ 2

theorem gainFor_pos {a : ℝ} (ha : 0 < a) : 0 < gainFor a := by
  obtain ⟨hd0, hd1, -⟩ := modulus_spec ha
  simp only [gainFor]
  nlinarith

theorem gainFor_lt_one {a : ℝ} (ha : 0 < a) : gainFor a < 1 := by
  obtain ⟨hd0, -, -⟩ := modulus_spec ha
  simp only [gainFor]
  nlinarith

/-- The gain on the distance that goes with it is `a² d`. -/
theorem gainE_gainFor {a : ℝ} (ha : 0 < a) : gainE (gainFor a) = a ^ 2 * modulus a := by
  obtain ⟨hd0, hd1, hrel⟩ := modulus_spec ha
  have h : (1 : ℝ) + modulus a ^ 2 ≠ 0 := by positivity
  simp only [gainE, gainFor]
  rw [show 2 - (1 - modulus a ^ 2) = 1 + modulus a ^ 2 by ring, div_eq_iff h]
  linarith

/-- **The law with the gain for `a` is the best for the weight `a⁴`.** -/
theorem weight_gainFor {a : ℝ} (ha : 0 < a) : weight (gainFor a) = a ^ 4 := by
  obtain ⟨hd0, hd1, hrel⟩ := modulus_spec ha
  have h1 : (1 : ℝ) + modulus a ^ 2 ≠ 0 := by positivity
  have h2 : modulus a ^ 2 ≠ 0 := by positivity
  simp only [weight, gainFor]
  rw [show 2 - (1 - modulus a ^ 2) = 1 + modulus a ^ 2 by ring,
    show 1 - (1 - modulus a ^ 2) = modulus a ^ 2 by ring, div_eq_iff (by positivity)]
  linear_combination
    -((1 - modulus a ^ 2) ^ 2 + a ^ 2 * modulus a * (1 + modulus a ^ 2)) * hrel

/-- The weight grows with the gain, so there is one gain for each weight. -/
theorem weight_strictMono {g₁ g₂ : ℝ} (h0 : 0 < g₁) (h12 : g₁ < g₂) (h1 : g₂ < 1) :
    weight g₁ < weight g₂ := by
  have ha : 0 < (2 - g₁) ^ 2 * (1 - g₁) := by
    have : 0 < 1 - g₁ := by linarith
    have : 0 < 2 - g₁ := by linarith
    positivity
  have hb : 0 < (2 - g₂) ^ 2 * (1 - g₂) := by
    have : 0 < 1 - g₂ := by linarith
    have : 0 < 2 - g₂ := by linarith
    positivity
  simp only [weight]
  rw [div_lt_div_iff₀ ha hb]
  have hnum : g₁ ^ 4 < g₂ ^ 4 := pow_lt_pow_left₀ h12 h0.le (by norm_num)
  have hden : (2 - g₂) ^ 2 * (1 - g₂) < (2 - g₁) ^ 2 * (1 - g₁) := by
    have hsq : (2 - g₂) ^ 2 < (2 - g₁) ^ 2 :=
      pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
    have h3 : 0 < 1 - g₂ := by linarith
    have h4 : 0 < (2 - g₁) ^ 2 := by
      have : 0 < 2 - g₁ := by linarith
      positivity
    nlinarith
  have h5 : 0 < g₁ ^ 4 := by positivity
  nlinarith

/-- The gain for `a` is the only gain strictly between 0 and 1 whose law is
the best for the weight `a⁴`. -/
theorem gain_unique {a g : ℝ} (ha : 0 < a) (hg0 : 0 < g) (hg1 : g < 1)
    (hw : weight g = a ^ 4) : g = gainFor a := by
  rcases lt_trichotomy g (gainFor a) with h | h | h
  · have := weight_strictMono hg0 h (gainFor_lt_one ha)
    rw [hw, weight_gainFor ha] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := weight_strictMono (gainFor_pos ha) h hg1
    rw [hw, weight_gainFor ha] at this
    exact absurd this (lt_irrefl _)

/-- Under the law for `a` a cycle multiplies the value by the square of the
modulus. -/
theorem value_step_gainFor {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    value (gainFor a) (step (gainFor a) x) = modulus a ^ 2 * value (gainFor a) x := by
  rw [value_step (gainFor_pos ha) (gainFor_lt_one ha)]
  simp only [gainFor]
  ring

end Unisono.Model.Regulation
