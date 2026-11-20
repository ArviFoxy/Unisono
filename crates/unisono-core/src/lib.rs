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
//! panicking macros and methods.

#![no_std]
#![forbid(unsafe_code)]
#![deny(
    clippy::arithmetic_side_effects,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::panic,
    clippy::todo,
    clippy::unimplemented,
    clippy::unreachable,
    clippy::unwrap_used
)]
// A cast written with `as` translates to Lean directly; `From` and `TryFrom`
// between integer types do not.
#![allow(clippy::cast_lossless)]

pub mod fixed;
