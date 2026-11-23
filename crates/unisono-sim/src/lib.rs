// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Deterministic discrete-event simulator of clocks, network links, and hosts.
//!
//! Runs the production [`unisono_runtime`] network and playback engines
//! (`SenderNetEngine`, `ReceiverNetEngine`, `ReceiverPlayback`,
//! `ReportSchedule`) over real serialized UDP wire bytes and simulated
//! IEEE 1139 clocks and impaired links, scoring playback against the six
//! canonical objectives of `Unisono.Spec.Objectives`.

#![forbid(unsafe_code)]

pub mod assumptions;
pub mod clock;
pub mod link;
pub mod objectives;
pub mod oracle;
pub mod packets;
pub mod protection;
pub mod random;
pub mod scene;

/// A point in true time, in nanoseconds from the start of a simulation.
///
/// No simulated party reads this; each reads its own [`clock::Oscillator`] or
/// [`clock::Course`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TrueTime(pub i64);

impl TrueTime {
    /// The start of a simulation.
    pub const ZERO: TrueTime = TrueTime(0);

    /// The true time `seconds` after the start.
    #[must_use]
    pub fn from_seconds(seconds: f64) -> TrueTime {
        TrueTime(seconds_to_nanos(seconds))
    }

    /// Seconds from the start.
    #[must_use]
    pub fn seconds(self) -> f64 {
        nanos_to_seconds(self.0)
    }

    /// This time moved by `seconds`, which may be negative.
    #[must_use]
    pub fn plus_seconds(self, seconds: f64) -> TrueTime {
        TrueTime(self.0.saturating_add(seconds_to_nanos(seconds)))
    }
}

/// A duration in seconds as the nearest whole number of nanoseconds.
#[must_use]
pub fn seconds_to_nanos(seconds: f64) -> i64 {
    // A float-to-integer cast saturates, which is the wanted behaviour at the ends.
    #[allow(clippy::cast_possible_truncation)]
    let nanos = (seconds * 1e9).round() as i64;
    nanos
}

/// A whole number of nanoseconds as seconds.
#[must_use]
pub fn nanos_to_seconds(nanos: i64) -> f64 {
    // Exact below 2^53 ns, which is 104 days.
    #[allow(clippy::cast_precision_loss)]
    let seconds = nanos as f64 * 1e-9;
    seconds
}
