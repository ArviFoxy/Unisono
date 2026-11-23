// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Real-time audio backend callback traits ([`Capture`] and [`Playback`]).
//!
//! Each audio backend invokes [`Capture::cycle`] or [`Playback::cycle`] once
//! per device period on its real-time audio thread, passing interleaved `f32`
//! frames, the device's running frame counter for the first frame in the
//! block, and the corresponding raw monotonic host timestamp (`CLOCK_MONOTONIC_RAW`,
//! in nanoseconds).
//!
//! Implementations execute in a hard real-time context and must not block,
//! allocate, or acquire locks.

/// What a playback device plays: it is asked for the frames of each cycle.
pub trait Playback {
    /// The number of samples in a frame.
    fn channels(&self) -> usize;

    /// Fills `frames` with what the device is to play in one cycle.
    ///
    /// `position` is the device's count of frames at the first frame of
    /// `frames`: a count that goes up by one for each frame the device
    /// plays, from wherever it started. `time` is the reading of the host's
    /// clock at which that first frame leaves the device, as the device
    /// reports it.
    fn cycle(&mut self, frames: &mut [f32], position: u64, time: i64);
}

/// What takes the frames of a capture device: it is given the frames of each
/// cycle.
pub trait Capture {
    /// The number of samples in a frame.
    fn channels(&self) -> usize;

    /// Takes the frames that the device captured in one cycle.
    ///
    /// `position` is the device's count of frames at the first frame of
    /// `frames`, and `time` the reading of the host's clock at which that
    /// frame was captured, as the device reports it.
    fn cycle(&mut self, frames: &[f32], position: u64, time: i64);
}
