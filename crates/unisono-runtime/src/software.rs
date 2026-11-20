// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! An audio device made of software.
//!
//! It has what a device of hardware has: a count of frames that advances at a
//! rate of its own against the host's clock, cycles of a fixed number of
//! frames, and a delay that it does not report. It has no clock of its own:
//! whoever drives it says what time it is, and the device runs the cycles
//! that are due by then. A test sets the time and so runs hours of audio in
//! a moment; a program that reads the time from a real clock, and waits for
//! the next cycle, has a device that discards what it plays, or produces
//! what its source computes.
//!
//! An [`Output`] keeps what it was given to play, and for every frame the
//! true time at which it would have left a device of hardware is known: see
//! [`Device::played`].

use crate::audio::{Capture, Playback};

/// The number of nanoseconds in a second, and of parts in a billion.
const BILLION: i128 = 1_000_000_000;

/// What a software device is like.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Device {
    /// Frames per second, nominally.
    pub rate: u32,
    /// The number of samples in a frame.
    pub channels: usize,
    /// The number of frames in a cycle.
    pub cycle: usize,
    /// How much faster than `rate` the device runs against the host's clock,
    /// in parts per billion.
    pub drift: i32,
    /// The reading of the host's clock that the device reports for the frame
    /// it counts as 0.
    pub start: i64,
    /// For playback, how long before the first frame of a cycle leaves the
    /// device the cycle is asked for; for capture, how long after the last
    /// frame of a cycle was captured the cycle is handed over. In
    /// nanoseconds.
    pub lead: i64,
    /// A delay that the device does not report, in nanoseconds: a frame
    /// leaves a playback device this much later than reported, and entered a
    /// capture device this much earlier.
    pub hidden: i64,
}

impl Device {
    /// The reading of the host's clock that the device reports for the frame
    /// it counts as `position`.
    #[must_use]
    pub fn reported(&self, position: u64) -> i64 {
        // Frames per billion seconds; at least one, so that a device with a
        // rate of zero does not divide by zero.
        let pace = (i128::from(self.rate) * (BILLION + i128::from(self.drift))).max(1);
        // A 64-bit count times 10^18 is below 2^124.
        let elapsed = i128::from(position) * BILLION * BILLION / pace;
        let time = i128::from(self.start).saturating_add(elapsed);
        i64::try_from(time).unwrap_or(i64::MAX)
    }

    /// The reading of the host's clock at which the frame that a playback
    /// device counts as `position` leaves it.
    #[must_use]
    pub fn played(&self, position: u64) -> i64 {
        self.reported(position).saturating_add(self.hidden)
    }

    /// The reading of the host's clock at which the frame that a capture
    /// device counts as `position` entered it.
    #[must_use]
    pub fn captured(&self, position: u64) -> i64 {
        self.reported(position).saturating_sub(self.hidden)
    }
}

/// A software device that plays.
///
/// It asks a [`Playback`] for the frames of each cycle and keeps them, up to
/// a number of frames set at the start, so that it allocates nothing while
/// it runs.
#[derive(Clone, Debug)]
pub struct Output {
    device: Device,
    /// The count of the first frame of the next cycle.
    position: u64,
    buffer: Box<[f32]>,
    record: Vec<f32>,
    /// Frames that were played after the record was full.
    unrecorded: u64,
}

impl Output {
    /// A device like `device` that keeps the first `record` frames it plays.
    #[must_use]
    pub fn new(device: Device, record: usize) -> Output {
        Output {
            device,
            position: 0,
            buffer: vec![0.0; device.cycle.saturating_mul(device.channels)].into_boxed_slice(),
            record: Vec::with_capacity(record.saturating_mul(device.channels)),
            unrecorded: 0,
        }
    }

    /// What the device is like.
    #[must_use]
    pub fn device(&self) -> &Device {
        &self.device
    }

    /// The count of the first frame of the next cycle.
    #[must_use]
    pub fn position(&self) -> u64 {
        self.position
    }

    /// The reading of the host's clock at which the next cycle is asked for.
    #[must_use]
    pub fn due(&self) -> i64 {
        self.device
            .reported(self.position)
            .saturating_sub(self.device.lead)
    }

    /// Runs one cycle: asks `playback` for its frames and keeps them. A
    /// `playback` whose frames have another number of samples than the
    /// device's is not asked, and the cycle is silent.
    pub fn cycle(&mut self, playback: &mut impl Playback) {
        if playback.channels() == self.device.channels {
            let time = self.device.reported(self.position);
            playback.cycle(&mut self.buffer, self.position, time);
        } else {
            self.buffer.fill(0.0);
        }
        if self.record.len() + self.buffer.len() <= self.record.capacity() {
            self.record.extend_from_slice(&self.buffer);
        } else {
            self.unrecorded = self.unrecorded.saturating_add(self.device.cycle as u64);
        }
        self.position = self.position.saturating_add(self.device.cycle as u64);
    }

    /// Runs the cycles that are asked for at or before the reading `now` of
    /// the host's clock, and returns how many that were.
    pub fn run(&mut self, now: i64, playback: &mut impl Playback) -> usize {
        let mut cycles = 0;
        // A device without frames in a cycle would never get past `now`.
        while self.device.cycle > 0 && self.due() <= now && self.position < u64::MAX {
            self.cycle(playback);
            cycles += 1;
        }
        cycles
    }

    /// The frames that were played, interleaved, from the frame counted as 0
    /// on, as far as they were kept.
    #[must_use]
    pub fn recorded(&self) -> &[f32] {
        &self.record
    }

    /// The number of frames that were played after the record was full.
    #[must_use]
    pub fn unrecorded(&self) -> u64 {
        self.unrecorded
    }
}

/// A software device that captures.
///
/// Its frames come from a function, which is given the count of a frame, the
/// true time at which that frame enters the device, and the frame to fill.
#[derive(Clone, Debug)]
pub struct Input<S> {
    device: Device,
    /// The count of the first frame of the next cycle.
    position: u64,
    buffer: Box<[f32]>,
    source: S,
}

impl<S: FnMut(u64, i64, &mut [f32])> Input<S> {
    /// A device like `device` that captures what `source` computes.
    #[must_use]
    pub fn new(device: Device, source: S) -> Input<S> {
        Input {
            device,
            position: 0,
            buffer: vec![0.0; device.cycle.saturating_mul(device.channels)].into_boxed_slice(),
            source,
        }
    }

    /// What the device is like.
    #[must_use]
    pub fn device(&self) -> &Device {
        &self.device
    }

    /// The count of the first frame of the next cycle.
    #[must_use]
    pub fn position(&self) -> u64 {
        self.position
    }

    /// The reading of the host's clock at which the next cycle is handed
    /// over: when its last frame has been captured, and the lead after.
    #[must_use]
    pub fn due(&self) -> i64 {
        let end = self.position.saturating_add(self.device.cycle as u64);
        self.device.reported(end).saturating_add(self.device.lead)
    }

    /// Runs one cycle: computes its frames and hands them to `capture`. A
    /// `capture` whose frames have another number of samples than the
    /// device's is given nothing.
    pub fn cycle(&mut self, capture: &mut impl Capture) {
        if self.device.channels > 0 {
            let frames = self.buffer.chunks_exact_mut(self.device.channels);
            for (frame, offset) in frames.zip(0u64..) {
                let position = self.position.saturating_add(offset);
                (self.source)(position, self.device.captured(position), frame);
            }
        }
        if capture.channels() == self.device.channels {
            let time = self.device.reported(self.position);
            capture.cycle(&self.buffer, self.position, time);
        }
        self.position = self.position.saturating_add(self.device.cycle as u64);
    }

    /// Runs the cycles that are handed over at or before the reading `now`
    /// of the host's clock, and returns how many that were.
    pub fn run(&mut self, now: i64, capture: &mut impl Capture) -> usize {
        let mut cycles = 0;
        while self.device.cycle > 0 && self.due() <= now && self.position < u64::MAX {
            self.cycle(capture);
            cycles += 1;
        }
        cycles
    }
}

#[cfg(test)]
mod tests {
    use super::{Device, Input, Output};
    use crate::audio::{Capture, Playback};

    fn device() -> Device {
        Device {
            rate: 50_000,
            channels: 2,
            cycle: 100,
            drift: 0,
            start: 1_000_000,
            lead: 3_000_000,
            hidden: 0,
        }
    }

    /// Plays, in each frame, the device's count of the frame and the time of
    /// the cycle, and remembers the cycles it was asked for.
    struct Counting {
        cycles: Vec<(u64, i64, usize)>,
    }

    impl Playback for Counting {
        fn channels(&self) -> usize {
            2
        }

        fn cycle(&mut self, frames: &mut [f32], position: u64, time: i64) {
            self.cycles.push((position, time, frames.len()));
            let first = u16::try_from(position).unwrap_or(0);
            for (frame, offset) in frames.as_chunks_mut::<2>().0.iter_mut().zip(0u16..) {
                *frame = [f32::from(first + offset), -1.0];
            }
        }
    }

    /// A frame of 50,000 a second lasts 20,000 nanoseconds exactly, so the
    /// expected times are whole numbers.
    #[test]
    fn frames_are_reported_at_the_device_s_rate_from_its_start() {
        let exact = device();
        assert_eq!(exact.reported(0), 1_000_000);
        assert_eq!(exact.reported(50_000), 1_001_000_000);
        // A device that is a thousandth fast takes a second for 50,050
        // frames.
        let fast = Device {
            drift: 1_000_000,
            ..exact
        };
        assert_eq!(fast.reported(50_050), 1_001_000_000);
        // Rounding is downward and does not add up: frame 3 of a device at
        // three frames a second is exactly a second on.
        let slow = Device { rate: 3, ..exact };
        assert_eq!(slow.reported(1), 1_000_000 + 333_333_333);
        assert_eq!(slow.reported(3), 1_001_000_000);
    }

    #[test]
    fn a_hidden_delay_moves_the_true_times_and_not_the_reported_ones() {
        let hiding = Device {
            hidden: 250_000,
            ..device()
        };
        assert_eq!(hiding.reported(100), device().reported(100));
        assert_eq!(hiding.played(100), hiding.reported(100) + 250_000);
        assert_eq!(hiding.captured(100), hiding.reported(100) - 250_000);
    }

    /// A cycle that is asked for too early or too late, or with the wrong
    /// count or time, would show here.
    #[test]
    fn an_output_asks_for_each_cycle_its_lead_before_the_cycle_leaves() {
        let mut output = Output::new(device(), 250);
        let mut playback = Counting { cycles: Vec::new() };
        // The first cycle leaves at 1 ms and is asked for at -2 ms; the
        // second leaves 2 ms later.
        assert_eq!(output.due(), -2_000_000);
        assert_eq!(output.run(-2_000_001, &mut playback), 0);
        assert_eq!(output.run(-2_000_000, &mut playback), 1);
        assert_eq!(output.run(3_999_999, &mut playback), 2);
        assert_eq!(
            playback.cycles,
            [
                (0, 1_000_000, 200),
                (100, 3_000_000, 200),
                (200, 5_000_000, 200)
            ]
        );
        assert_eq!(output.position(), 300);
    }

    #[test]
    fn an_output_keeps_what_it_played_as_far_as_it_has_room() {
        let mut output = Output::new(device(), 250);
        let mut playback = Counting { cycles: Vec::new() };
        // Three cycles are asked for before 4 ms.
        assert_eq!(output.run(3_999_999, &mut playback), 3);
        // Room for 250 frames holds two whole cycles; the third is counted.
        let recorded = output.recorded();
        assert_eq!(recorded.len(), 400);
        assert_eq!(recorded[0..2], [0.0, -1.0]);
        assert_eq!(recorded[398..400], [199.0, -1.0]);
        assert_eq!(output.unrecorded(), 100);
    }

    /// Remembers what it was given.
    struct Taking {
        cycles: Vec<(u64, i64)>,
        frames: Vec<f32>,
    }

    impl Capture for Taking {
        fn channels(&self) -> usize {
            2
        }

        fn cycle(&mut self, frames: &[f32], position: u64, time: i64) {
            self.cycles.push((position, time));
            self.frames.extend_from_slice(frames);
        }
    }

    #[test]
    fn an_input_hands_over_each_cycle_once_it_is_captured() {
        let hiding = Device {
            hidden: 250_000,
            ..device()
        };
        let mut times = Vec::new();
        let mut input = Input::new(hiding, |position, time, frame: &mut [f32]| {
            if position < 2 {
                times.push(time);
            }
            frame[0] = 0.5;
            frame[1] = if position < 100 { 0.25 } else { -0.25 };
        });
        let mut capture = Taking {
            cycles: Vec::new(),
            frames: Vec::new(),
        };
        // The last frame of the first cycle is captured by 3 ms; the cycle
        // is handed over 3 ms later.
        assert_eq!(input.due(), 6_000_000);
        assert_eq!(input.run(5_999_999, &mut capture), 0);
        assert_eq!(input.run(8_000_000, &mut capture), 2);
        assert_eq!(capture.cycles, [(0, 1_000_000), (100, 3_000_000)]);
        assert_eq!(capture.frames.len(), 400);
        assert_eq!(capture.frames[198..202], [0.5, 0.25, 0.5, -0.25]);
        drop(input);
        // The sound entered the device earlier than the device reports.
        assert_eq!(times, [750_000, 770_000]);
    }

    #[test]
    fn a_device_without_frames_in_a_cycle_runs_no_cycles() {
        let none = Device {
            cycle: 0,
            ..device()
        };
        let mut output = Output::new(none, 10);
        let mut playback = Counting { cycles: Vec::new() };
        assert_eq!(output.run(i64::MAX, &mut playback), 0);
    }
}
