// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! What an audio system and unisono ask of each other.
//!
//! An audio device works in cycles: it takes or gives a block of frames at a
//! time, and it counts the frames that pass. A backend for an audio system
//! calls one of the two traits here once for each cycle, on the thread that
//! the audio system runs the cycle on. Besides the frames it says which frame
//! of the device the block begins with, and when that frame passes the
//! device on the host's clock. Nothing else crosses the boundary, so a
//! backend is small, and the code behind the traits knows no audio system.
//!
//! Frames are interleaved: the samples of one frame side by side, one for
//! each channel. The host's clock is the raw monotonic clock, in nanoseconds.
//!
//! An implementation is called where audio must not wait: it takes no lock,
//! allocates nothing and does not block.

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
