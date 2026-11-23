// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Pure, panic-free, allocation-free protocol and timing core of `unisono`.
//!
//! Performs no I/O, clock reads, or heap allocation, enabling direct
//! translation to Lean via Charon/Aeneas for formal verification. Compile-time
//! lints forbid integer overflow, out-of-bounds indexing, and panicking APIs
//! outside tests.

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
// The translation to Lean is made with the configuration `translating` set,
// under which no type derives `Debug`: what `Debug` prints is no part of what
// is proved, and its code would only be carried along.
//
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

pub mod answers;
pub mod arrivals;
pub mod blue;
pub mod device;
pub mod fixed;
pub mod kalman;
pub mod min_rtt;
pub mod needs;
pub mod packet;
pub mod player;
pub mod presence;
pub mod receiver;
pub mod relation;
pub mod sender;
pub mod sync;
pub mod timing;
