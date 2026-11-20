// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The pure core of unisono.
//!
//! Nothing in this crate performs input or output, reads a clock, allocates
//! memory or can panic. Every function is a plain computation on its
//! arguments, which is what lets the crate be translated to Lean and have its
//! properties proved there.
//!
//! The lints below turn the constructs that can panic into compile errors:
//! arithmetic that can overflow, indexing that can be out of bounds, and the
//! panicking macros and methods. Tests are exempt, since a test fails by
//! panicking.

#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(
    not(test),
    deny(
        clippy::arithmetic_side_effects,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::panic,
        clippy::todo,
        clippy::unimplemented,
        clippy::unreachable,
        clippy::unwrap_used
    )
)]
// A cast written with `as` translates to Lean directly; `From` and `TryFrom`
// between integer types do not. Neither do `Option::copied`, a closure that
// returns a reference, and `?` on an `Option`, so an `Option` is taken apart
// with `match` or `let ... else`. `clamp` panics when its bounds are out of
// order, so a value is limited with two comparisons.
#![allow(
    clippy::cast_lossless,
    clippy::manual_clamp,
    clippy::manual_map,
    clippy::question_mark
)]

#[cfg(test)]
extern crate std;

pub mod arrivals;
pub mod device;
pub mod fixed;
pub mod packet;
pub mod player;
pub mod presence;
pub mod receiver;
pub mod relation;
pub mod sender;
pub mod timing;
