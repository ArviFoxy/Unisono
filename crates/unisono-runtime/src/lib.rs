// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The shell around unisono's core.
//!
//! The core computes; this crate does what touches the outside: it reads
//! clocks, sends and receives datagrams with the times the kernel stamped
//! them with, and passes items between threads without locks.

#![warn(clippy::undocumented_unsafe_blocks)]

pub mod clock;
pub mod ring;
pub mod socket;
