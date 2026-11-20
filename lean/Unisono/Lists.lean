/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Aeneas

/-!
# Writing to a place of a list that may not exist

Rust's `get_mut` gives the place of an element if there is one, and a write
through it translates to `List.set_opt`: the list, the place, and the new
value if the place exists.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Unisono.Lists

theorem set_opt_some {α : Type} (l : List α) (i : ℕ) (x : α) :
    l.set_opt i (some x) = l.set i x := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp [ih]

theorem set_opt_none {α : Type} (l : List α) (i : ℕ) : l.set_opt i none = l := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp [ih]

end Unisono.Lists
