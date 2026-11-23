// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Exported `cdylib` wrappers for audio-thread playback and capture cycles
//! audited by `tools/realtime.sh` for allocation-, panic-, and syscall-free
//! machine code.

// The entry points are named for the inspection, not for a caller in C.
#![allow(improper_ctypes_definitions)]

use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::receive::ReceiverAudio;
use unisono_runtime::send::CaptureEnd;

/// A receiver's audio thread as the program makes it.
pub type Audio = ReceiverAudio<256, 64, 8, 64>;

/// One cycle of a receiver's playback with a runtime-sized output slice.
#[unsafe(no_mangle)]
pub extern "C" fn realtime_playback_cycle(
    audio: &mut Audio,
    frames: &mut [f32],
    position: u64,
    time: i64,
) {
    audio.cycle(frames, position, time);
}

/// One cycle of a sender's capture with a runtime-sized input slice.
#[unsafe(no_mangle)]
pub extern "C" fn realtime_capture_cycle(
    end: &mut CaptureEnd,
    frames: &[f32],
    position: u64,
    time: i64,
) {
    end.cycle(frames, position, time);
}

/// A function that panics when `place` is beyond four, built only with the
/// feature `panic-probe`, so that `tools/realtime.sh` can see the check fail.
#[cfg(feature = "panic-probe")]
#[unsafe(no_mangle)]
pub extern "C" fn realtime_panic_probe(values: &[u8; 4], place: usize) -> u8 {
    #[allow(clippy::indexing_slicing)]
    values[place]
}
