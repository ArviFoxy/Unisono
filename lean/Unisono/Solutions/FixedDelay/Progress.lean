/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Memory
public import Unisono.Spec.Run
public import Unisono.Spec.Models.Bounded

/-!
# The baseline in a bounded world: progress

The baseline sets no timers, and what it sends at each event weighs less
than what the event uses up, a question weighing one more than the copies
of the answer it may draw. So in every world within bounds its run has an
event after every true time (`progress`), and it handles every request of
every speaker (`request_step`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- The weight of a message of the baseline: what it may lead to. A question
weighs one more than the copies of the answer it may draw. -/
def weight : Payload → ℕ
  | .block _ _ => 1
  | .ask _ => 1 + p.copies
  | .answer _ _ => 1

omit [DecidableEq H] in
/-- The copies of a message of weight one to each host of a list weigh one
per copy and host. -/
theorem weight_copies (l : List H) (c : ℕ) (x : Payload × Finset ℕ) (hx : weight p x.1 = 1) :
    ((l.flatMap fun j => List.replicate c (j, x)).map fun s => weight p s.2.1).sum
      = c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, hx, smul_eq_mul, mul_one, List.length_cons]
    ring

/-- **The baseline's run advances past every true time.** In a world within
bounds, the baseline sets no timers, and what it sends at each event weighs
less than what the event uses up, so it has an event after every true
time. -/
theorem progress (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (T : Time) : ∃ n, T < (solution p : Solution H R Payload).eventTime w lookahead n := by
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, -, -, -⟩ := hw
  refine Solution.progress w (solution p) lookahead (weight p)
    (p.copies * (p.speakers.filter (· ≠ p.sender)).length + 1) (p.copies * (1 + p.copies) + 1)
    ?_ ?_ ?_ ?_ (CaptureDevice.handed_unbounded w.rate_pos hsrc B.deviceRate_lt_one)
    (fun r => PlaybackDevice.asked_unbounded w.rate_pos (hspk r) B.deviceRate_lt_one (hlead r)) T
  · intro h view
    unfold solution act
    split
    · split <;> (try split) <;> (try split) <;> simp
    · rfl
  · intro h view frames rep reading
    rw [solution_append]
    simp only [act]
    split_ifs
    · split
      · rw [weight_copies p _ _ _ rfl]
      · simp
    · simp
  · intro h view r outs rep reading
    rw [solution_append]
    simp only [act]
    split_ifs <;> simp [weight, List.sum_replicate]
  · intro h view i c F reading
    rw [solution_append]
    cases c with
    | block f s => simp [act, weight]
    | ask sent =>
      simp only [act]
      split_ifs <;> simp [weight, List.sum_replicate]
    | answer s r => simp [act, weight]

/-- **Every request is handled.** In a world within bounds, the baseline's
run handles every request of every speaker at some step. -/
theorem request_step (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (r : Fin R) (b : ℕ) :
    ∃ n, ((solution p : Solution H R Payload).states w lookahead n).askedNext r = b ∧
      earliest (((solution p : Solution H R Payload).states w lookahead n).key w)
        ((solution p : Solution H R Payload).states w lookahead n).due = some (.asked r b) := by
  obtain ⟨m, hm⟩ := progress p w B hw lookahead ((w.speaker r).asked b)
  obtain ⟨n, -, h1, h2⟩ := Solution.exists_asked_step w (solution p) lookahead
    (Solution.lt_askedNext (solution p) w lookahead hm)
  exact ⟨n, h1, h2⟩

end Unisono.Solutions.FixedDelay
