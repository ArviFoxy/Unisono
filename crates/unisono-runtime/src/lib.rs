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
//! - [`memory`]: keeping the program's memory in place;
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
//!   for audio, and what passes between them;
//! - [`send`]: the two threads of a sender, one for capture and one for the
//!   network;
//! - [`level`]: the choice of the level from the needs that receivers
//!   report, which the sender's network thread makes.

#![warn(clippy::undocumented_unsafe_blocks)]

use std::{fmt, io};

/// A configuration validation error returned when settings violate a runtime
/// invariant (for example a zero rate, non-finite cost weight, or oversized
/// packet).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidSettings {
    message: &'static str,
}

impl InvalidSettings {
    /// Creates an invalid-settings error with a static diagnostic message.
    #[must_use]
    pub const fn new(message: &'static str) -> InvalidSettings {
        InvalidSettings { message }
    }

    /// The diagnostic message.
    #[must_use]
    pub const fn message(self) -> &'static str {
        self.message
    }
}

impl fmt::Display for InvalidSettings {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message)
    }
}

impl std::error::Error for InvalidSettings {}

impl From<InvalidSettings> for io::Error {
    fn from(error: InvalidSettings) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidInput, error.message)
    }
}

pub mod asking;
pub mod audio;
pub mod clock;
pub mod level;
pub mod memory;
pub mod network_thread;
pub mod proxy;
pub mod pump;
pub mod receive;
pub mod ring;
pub mod send;
pub mod socket;
pub mod software;
pub mod store;
pub mod syscalls;
