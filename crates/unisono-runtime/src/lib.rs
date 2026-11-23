// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Runtime I/O, threading, audio backend interfaces, and packet transport
//! layer around `unisono_core`.
//!
//! `unisono_core` contains pure, allocation-free protocol and timing logic;
//! this crate supplies the operating-system integration:
//!
//! - [`audio`]: real-time `Capture` and `Playback` callback traits for audio
//!   backends;
//! - [`clock`]: raw monotonic clock access and cross-domain timestamp
//!   conversion (`CLOCK_REALTIME` / `CLOCK_MONOTONIC` to `CLOCK_MONOTONIC_RAW`);
//! - [`level`]: sender-side adaptive playout latency selection from receiver
//!   need reports;
//! - [`memory`]: `mlockall` memory locking and stack prefaulting for real-time
//!   threads;
//! - [`network_thread`]: managed background thread with bounded stack and
//!   seccomp syscall restriction;
//! - [`proxy`]: deterministic UDP impairment proxy for testing delay, jitter,
//!   loss, pauses, reordering, and duplication;
//! - [`pump`]: bridges core playback plans, the sample store, concealment, and
//!   the resampler into output audio frames;
//! - [`receive`]: receiver network/audio thread bridge and lock-free rings;
//! - [`retransmission`]: missing-frame gap tracking and retry scheduling;
//! - [`ring`]: bounded lock-free single-producer single-consumer (SPSC) ring;
//! - [`send`]: sender capture/network thread bridge and packet transmission;
//! - [`socket`]: non-blocking UDP socket with kernel RX/TX timestamping;
//! - [`store`]: fixed-capacity ring buffer holding received PCM frames;
//! - [`syscalls`]: Linux seccomp-BPF syscall allowlist for network threads;
//! - [`virtual_device`]: externally clocked virtual capture and playback
//!   devices for tests and CLI software mode.

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

pub mod audio;
pub mod clock;
pub mod level;
pub mod memory;
pub mod network_thread;
pub mod proxy;
pub mod pump;
pub mod receive;
pub mod retransmission;
pub mod ring;
pub mod send;
pub mod socket;
pub mod store;
pub mod syscalls;
pub mod virtual_device;
