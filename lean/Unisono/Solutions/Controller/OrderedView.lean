/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Timing
public import Unisono.Spec.ViewOrder

/-!
# The timing rules on a view whose events are in the order of time

The readings of the events in a host's view never decrease
(`Unisono.Spec.Solution.views_pairwise`). This file states what the rules of
`Unisono.Solutions.Controller.Timing` take from such a view.

* `arrivalsOf_pairwise`: the arrivals of the view are in the order of the
  host's readings at them.
* `arrivalSlope_eq_of_pairwise`: the slope comes from the arrival `a` with
  the largest reading and from an arrival `a'` at least `baseline` older.
  Given any arrival `c` that is at least `baseline` older than some
  arrival, `a'` is no older than `c`. So when the view holds two arrivals of
  a recent stretch of time that are `baseline` apart, both arrivals of the
  slope lie in that stretch.
* `windowArrivals_eq_filter`, `mem_windowArrivals_iff`: when some arrival
  lies within `window` before the request, the estimate uses exactly the
  arrivals that do.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Model.Descent

variable {H : Type} {R : ℕ}

/-- **The arrivals of a view whose readings never decrease are in the order
of the host's readings.** -/
theorem arrivalsOf_pairwise {l : List (Event H R Payload)}
    (hl : l.Pairwise fun e e' => e.reading ≤ e'.reading) :
    (arrivalsOf l).Pairwise fun a a' => a.1 ≤ a'.1 := by
  unfold arrivalsOf
  refine hl.filterMap _ ?_
  intro e e' hee' a ha a' ha'
  split at ha
  · split at ha'
    · obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj ha'
      exact hee'
    · exact absurd ha' (by simp)
  · exact absurd ha (by simp)

/-- **The two arrivals of the slope.** Let the arrivals of a view be in the
order of the host's readings, and let the view hold an arrival `c` and an
arrival `aN` whose reading is at least `baseline > 0` later. Then the slope
that the host takes is, kept within `slopeBound` of one, the slope between
two arrivals `a` and `a'` of the view: `a` is no older than `aN`, `a'` is
no older than `c`, and `a'` is at least `baseline` older than `a`. -/
theorem arrivalSlope_eq_of_pairwise (t : TimingSettings) (hbase : 0 < t.baseline)
    {view : List (Event H R Payload)}
    (hsorted : (arrivalsOf view).Pairwise fun a a' => a.1 ≤ a'.1) {c aN : ℝ × ℝ}
    (hc : c ∈ arrivalsOf view) (haN : aN ∈ arrivalsOf view) (hcN : c.1 + t.baseline ≤ aN.1) :
    ∃ a ∈ arrivalsOf view, ∃ a' ∈ arrivalsOf view, aN.1 ≤ a.1 ∧ c.1 ≤ a'.1
      ∧ a'.1 + t.baseline ≤ a.1
      ∧ arrivalSlope t view
        = clampTo (1 - t.slopeBound) (1 + t.slopeBound) ((a.2 - a'.2) / (a.1 - a'.1)) := by
  cases hrev : (arrivalsOf view).reverse with
  | nil =>
    rw [List.reverse_eq_nil_iff] at hrev
    rw [hrev] at haN
    simp at haN
  | cons a rest =>
    have hL : arrivalsOf view = rest.reverse ++ [a] := List.reverse_eq_cons_iff.mp hrev
    rw [hL] at hsorted hc haN
    obtain ⟨hrestS, -, hlast⟩ := List.pairwise_append.mp hsorted
    have hrest : rest.Pairwise fun x y => y.1 ≤ x.1 := List.pairwise_reverse.mp hrestS
    have hle : ∀ x ∈ rest.reverse ++ [a], x.1 ≤ a.1 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hlast x hx a (List.mem_singleton.mpr rfl)
      · rw [List.mem_singleton] at hx
        rw [hx]
    have haNa := hle aN haN
    have hca : c.1 ≤ a.1 - t.baseline := by linarith
    have hcrest : c ∈ rest := by
      rcases List.mem_append.mp hc with hx | hx
      · exact List.mem_reverse.mp hx
      · rw [List.mem_singleton] at hx
        rw [hx] at hca
        linarith
    cases hfind : rest.find? (fun a' => decide (a'.1 ≤ a.1 - t.baseline)) with
    | none =>
      have h1 := List.find?_eq_none.mp hfind c hcrest
      simp only [decide_eq_true_eq] at h1
      exact absurd hca h1
    | some a' =>
      obtain ⟨hp, as, bs, hsplit, has⟩ := List.find?_eq_some_iff_append.mp hfind
      have hpa : a'.1 ≤ a.1 - t.baseline := by simpa using hp
      have ha'rest : a' ∈ rest := by
        rw [hsplit]
        simp
      have hca' : c.1 ≤ a'.1 := by
        rw [hsplit] at hcrest hrest
        rcases List.mem_append.mp hcrest with hx | hx
        · have h1 := has c hx
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
          exact absurd hca h1
        · rcases List.mem_cons.mp hx with hx | hx
          · rw [hx]
          · exact (List.pairwise_cons.mp (List.pairwise_append.mp hrest).2.1).1 c hx
      refine ⟨a, ?_, a', ?_, haNa, hca', by linarith, ?_⟩
      · rw [hL]
        simp
      · rw [hL]
        exact List.mem_append_left _ (List.mem_reverse.mpr ha'rest)
      · unfold arrivalSlope
        rw [hrev]
        simp only [hfind]

/-- **When some arrival lies within `window` before the request, the
estimate uses the arrivals that do.** -/
theorem windowArrivals_eq_filter (t : TimingSettings) {l : List (Event H R Payload)}
    {e : Event H R Payload} {a₁ : ℝ × ℝ} (h₁ : a₁ ∈ arrivalsOf (l ++ [e]))
    (hw : e.reading - t.window ≤ a₁.1) :
    windowArrivals t (l ++ [e])
      = (arrivalsOf (l ++ [e])).filter fun a => decide (e.reading - t.window ≤ a.1) := by
  have hmem : a₁ ∈ (arrivalsOf (l ++ [e])).filter
      (fun a => decide (e.reading - t.window ≤ a.1)) :=
    List.mem_filter.mpr ⟨h₁, by simpa using hw⟩
  unfold windowArrivals
  rw [List.getLast?_concat]
  simp only
  cases hf : (arrivalsOf (l ++ [e])).filter (fun a => decide (e.reading - t.window ≤ a.1)) with
  | nil =>
    rw [hf] at hmem
    simp at hmem
  | cons a as => rfl

/-- **The arrivals that the estimate uses, when some arrival lies within
`window` before the request**: the arrivals of the view at which the host's
clock read at most `window` less than at the request. -/
theorem mem_windowArrivals_iff (t : TimingSettings) {l : List (Event H R Payload)}
    {e : Event H R Payload} {a₁ : ℝ × ℝ} (h₁ : a₁ ∈ arrivalsOf (l ++ [e]))
    (hw : e.reading - t.window ≤ a₁.1) {a : ℝ × ℝ} :
    a ∈ windowArrivals t (l ++ [e])
      ↔ a ∈ arrivalsOf (l ++ [e]) ∧ e.reading - t.window ≤ a.1 := by
  rw [windowArrivals_eq_filter t h₁ hw, List.mem_filter]
  simp

end Unisono.Solutions.Controller
