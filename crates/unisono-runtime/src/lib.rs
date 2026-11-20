// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The shell around unisono's core.
//!
//! The core decides; this crate does what the core cannot: it reads clocks,
//! sends and receives datagrams, passes items between threads, holds
//! samples, talks to audio systems, and moves frames. Its parts:
//!
//! - [`clock`]: the host's clocks, and the clock that the kernel stamps
//!   packets with against the clock that everything else is timed by;
//! - [`socket`]: datagrams with the times at which the kernel saw them
//!   arrive and leave;
//! - [`ring`]: a ring between two threads that neither end waits at;
//! - [`proxy`]: a proxy for tests that delays, drops, pauses, reorders and
//!   duplicates datagrams;
//! - [`audio`]: what an audio system and unisono ask of each other, once for
//!   each cycle of a device;
//! - [`software`]: an audio device made of software, driven by a clock that
//!   its user sets;
//! - [`store`]: the samples of the frames that a receiver holds;
//! - [`pump`]: what turns the core's plan for a cycle into the frames that
//!   the device plays;
//! - [`receive`]: the two threads of a receiver, one for the network and one
//!   for audio, and what passes between them.

#![warn(clippy::undocumented_unsafe_blocks)]

pub mod audio;
pub mod clock;
pub mod proxy;
pub mod pump;
pub mod receive;
pub mod ring;
pub mod socket;
pub mod software;
pub mod store;
