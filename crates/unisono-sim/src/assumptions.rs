// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Sets of assumptions about hosts and links, with numbers.
//!
//! A test names the set it runs under and holds its result against a number.
//! The sets are what the tests assume, not what any real link was measured
//! to do: a test that passes says that the code does what it should where the
//! world is as assumed, and nothing about where it is not.

use crate::link::LinkModel;

/// What is assumed of a sender, a receiver and the link from one to the other.
#[derive(Clone, Copy, Debug)]
pub struct OneWayAssumptions {
    /// A name for reports.
    pub name: &'static str,
    /// The link from the sender to the receiver.
    pub link: LinkModel,
    /// Variance that each oscillator's fractional frequency gains per second.
    pub frequency_walk: f64,
    /// Packets per second.
    pub packet_rate: f64,
}

/// A switched wired network with little other traffic. Nine packets in ten
/// pass with a few microseconds of excess delay; the rest wait behind another
/// frame.
pub const WIRED_CALM: OneWayAssumptions = OneWayAssumptions {
    name: "wired, calm",
    link: LinkModel {
        minimum: 100e-6,
        clear_excess: 5e-6,
        queued: 0.1,
        queued_excess: 200e-6,
        pause_rate: 0.0,
        pause_length: 0.0,
    },
    frequency_walk: 1e-19,
    packet_rate: 750.0,
};

/// A wired network under load: most packets wait in a queue, and a pause of
/// tens of milliseconds comes about once a minute.
pub const WIRED_BUSY: OneWayAssumptions = OneWayAssumptions {
    name: "wired, busy",
    link: LinkModel {
        minimum: 100e-6,
        clear_excess: 20e-6,
        queued: 0.6,
        queued_excess: 500e-6,
        pause_rate: 1.0 / 60.0,
        pause_length: 30e-3,
    },
    frequency_walk: 1e-18,
    packet_rate: 750.0,
};

/// A wireless link: half the packets wait for the medium, and about once a
/// minute the link pauses for about a second. The smallest delay is taken as
/// constant, which a real wireless link that changes its rate does not keep.
pub const WIRELESS: OneWayAssumptions = OneWayAssumptions {
    name: "wireless",
    link: LinkModel {
        minimum: 1e-3,
        clear_excess: 300e-6,
        queued: 0.5,
        queued_excess: 3e-3,
        pause_rate: 1.0 / 60.0,
        pause_length: 1.0,
    },
    frequency_walk: 1e-18,
    packet_rate: 750.0,
};
