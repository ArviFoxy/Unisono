# Rust in the core

`crates/unisono-core` is translated to Lean by
[Aeneas](https://github.com/AeneasVerif/aeneas), and the theorems are proved
about the translation. The core is therefore written in the part of Rust that
Aeneas translates, and so that no function in it can panic. This page records
what that part is. It was found by translating a test crate of 109 functions
at the Aeneas commit that `tools/proof-tools.sh` pins, and it is to be checked
again whenever that commit changes.

## What translates

- Integers of every width, including 128 bits: comparisons, `as` casts, bit
  operations, shifts, and the methods `checked_add`, `checked_sub`,
  `checked_mul`, `checked_rem`, `wrapping_add`, `wrapping_sub`, `wrapping_mul`,
  `wrapping_shl`, `wrapping_shr`, `saturating_add`, `saturating_sub`,
  `leading_zeros`, `min`, `max`, `from_le_bytes` and `to_le_bytes`.
- Structs, tuple structs and enums with data; `match` with guards and nested
  patterns, `if let`, `let … else` and `matches!`.
- `Option` and `Result`, `?` on a `Result`, and `Option::unwrap_or`.
- Traits with associated constants and default methods, generic functions
  with trait bounds, and const generics.
- Arrays and slices: `len`, `get`, `get_mut`, `split_at`, `fill`, a sub-range
  taken with `get`.
- `while` loops, and `for` over a range or over the iterator of a slice.
- `&mut` to a field, a function that returns `&mut`, `core::mem::replace`,
  `core::mem::swap` and `Option::take`.
- The derives `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord` and
  `Debug`.

## What does not

A function of the standard library that Aeneas has no Lean model for enters
the translation as an axiom, or as a definition left for someone to fill in.
`tools/extract.sh` fails when either happens. The ones met so far:

- `?` on an `Option`; write a `match` or `let … else`;
- `div_euclid`, `rem_euclid`, `wrapping_neg`, `unsigned_abs`, `is_negative`,
  `abs_diff` and `checked_shl`;
- `TryFrom` between integer types, `Result::ok` and `first` on a slice.

Three constructs fail to translate or bring in such a function:

- taking an array apart by value (`let [a, b] = array;`);
- a closure that returns a reference, as in `.and_then(|i| slice.get(*i))`,
  and `Option::copied`; an `Option` is taken apart with `match` instead;
- a derived `Debug` on a type with a field that is an `Option` or a tuple.

`Debug` is therefore not translated at all. The translation is made with the
configuration `translating` set, and every type of the core derives `Debug`
with `#[cfg_attr(not(translating), derive(Debug))]`. What `Debug` prints is
no part of what is proved.

That is the only use of the configuration. A function of the core that was
compiled only when not translating would be code that no theorem and no
comparison covers, in the crate whose every function is proved to return.
`tools/extract.sh` refuses a core that has one. What cannot be translated
belongs in another crate.

Three things translate into Lean that then does not serve:

- a field with the name of a module whose types a later field of the same
  struct uses: in the Lean structure the field's name hides the module's.
  The field gets another name;
- a constant written as a computation, such as `1 << 40`: it becomes a
  computation in Lean too, and proofs that meet it run out of time. Constants
  are written as plain numbers;
- `clamp`, which fails when its bounds are out of order: a value is limited
  with two comparisons instead.

## Rules of the core

- **Nothing panics.** The lints at the top of `src/lib.rs` reject the
  arithmetic operators, indexing with `[]`, `unwrap`, `expect` and the
  panicking macros. Arithmetic is written with the `checked_`, `wrapping_` or
  `saturating_` methods. Where a wrapping operation cannot wrap, a comment
  says why and the proof shows it.
- **No floating point.** The core computes on integers and fixed-point
  numbers, so that its results are the same on every platform and are what
  the proofs are about.
- **No `unsafe`, no interior mutability, no allocation.** State is passed in
  and out explicitly.
