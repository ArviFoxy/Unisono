// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Virtual audio capture and playback devices.
//!
//! Models an audio device's frame counter, fixed-size cycles, clock drift
//! relative to the host clock, callback lead time, and unreported hardware
//! latency without binding to an OS audio backend. The caller advances time
//! explicitly via `run(now, ...)`, enabling deterministic accelerated tests
//! as well as real-time software signal generation and sink recording.
//!
//! [`Output`] records rendered samples into a fixed-capacity buffer, and
//! [`Device::played`] / [`Device::captured`] compute the exact host-clock
//! timestamp for any frame index.

use crate::audio::{Capture, Playback};

/// Nanoseconds per second (and parts per billion).
const BILLION: i128 = 1_000_000_000;

/// Timing and format parameters for a software audio device.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Device {
    /// Nominal sample rate in frames per second.
    pub rate: u32,
    /// Number of interleaved channels per frame.
    pub channels: usize,
    /// Number of frames processed per audio callback cycle.
    pub cycle: usize,
    /// Clock drift relative to the host clock, in parts per billion.
    pub drift: i32,
    /// Host-clock timestamp (ns) reported for frame 0.
    pub start: i64,
    /// Callback scheduling offset in nanoseconds: for playback, how early a
    /// cycle is requested before its first frame plays; for capture, how late
    /// a cycle is delivered after its last frame is captured.
    pub lead: i64,
    /// Unreported hardware latency in nanoseconds (added to playback times,
    /// subtracted from capture times).
    pub hidden: i64,
}

impl Device {
    /// Returns the host-clock timestamp (ns) reported by the device for frame
    /// `position`.
    #[must_use]
    pub fn reported(&self, position: u64) -> i64 {
        // Frames per billion seconds, clamped to >= 1 to avoid division by zero.
        let pace = (i128::from(self.rate) * (BILLION + i128::from(self.drift))).max(1);
        // u64 * 10^18 fits well inside i128 (< 2^124).
        let elapsed = i128::from(position) * BILLION * BILLION / pace;
        let time = i128::from(self.start).saturating_add(elapsed);
        i64::try_from(time).unwrap_or(i64::MAX)
    }

    /// Returns the actual host-clock timestamp (ns) at which playback frame
    /// `position` leaves the DAC (including unreported hardware latency).
    #[must_use]
    pub fn played(&self, position: u64) -> i64 {
        self.reported(position).saturating_add(self.hidden)
    }

    /// Returns the actual host-clock timestamp (ns) at which capture frame
    /// `position` entered the ADC (excluding unreported hardware latency).
    #[must_use]
    pub fn captured(&self, position: u64) -> i64 {
        self.reported(position).saturating_sub(self.hidden)
    }
}

/// Software playback device that invokes a [`Playback`] callback per cycle
/// and stores rendered frames in a preallocated buffer.
#[derive(Clone, Debug)]
pub struct Output {
    device: Device,
    /// Index of the first frame in the next cycle.
    position: u64,
    buffer: Box<[f32]>,
    record: Vec<f32>,
    /// Frames played after `record` reached capacity.
    unrecorded: u64,
}

impl Output {
    /// Creates a playback device that records up to `record` rendered frames
    /// without allocating during cycles.
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

    /// Returns the device configuration.
    #[must_use]
    pub fn device(&self) -> &Device {
        &self.device
    }

    /// Returns the starting frame index of the next cycle.
    #[must_use]
    pub fn position(&self) -> u64 {
        self.position
    }

    /// Returns the host-clock timestamp (ns) when the next playback cycle is
    /// due to be requested.
    #[must_use]
    pub fn due(&self) -> i64 {
        self.device
            .reported(self.position)
            .saturating_sub(self.device.lead)
    }

    /// Executes one playback cycle. If `playback.channels()` does not match
    /// `self.device.channels`, outputs silence without calling `playback`.
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

    /// Runs all playback cycles due at or before host-clock timestamp `now`
    /// (ns) and returns the number of cycles executed.
    pub fn run(&mut self, now: i64, playback: &mut impl Playback) -> usize {
        let mut cycles = 0;
        // Guard against infinite loops when `cycle == 0`.
        while self.device.cycle > 0 && self.due() <= now && self.position < u64::MAX {
            self.cycle(playback);
            cycles += 1;
        }
        cycles
    }

    /// Returns the recorded interleaved samples starting from frame 0.
    #[must_use]
    pub fn recorded(&self) -> &[f32] {
        &self.record
    }

    /// Returns the number of frames played after the recording buffer filled.
    #[must_use]
    pub fn unrecorded(&self) -> u64 {
        self.unrecorded
    }
}

/// Software capture device that generates input frames from a closure
/// `(frame_index, capture_time_ns, frame_slice)` and delivers each cycle to a
/// [`Capture`] implementation.
#[derive(Clone, Debug)]
pub struct Input<S> {
    device: Device,
    /// Index of the first frame in the next cycle.
    position: u64,
    buffer: Box<[f32]>,
    source: S,
}

impl<S: FnMut(u64, i64, &mut [f32])> Input<S> {
    /// Creates a capture device driven by signal generator `source`.
    #[must_use]
    pub fn new(device: Device, source: S) -> Input<S> {
        Input {
            device,
            position: 0,
            buffer: vec![0.0; device.cycle.saturating_mul(device.channels)].into_boxed_slice(),
            source,
        }
    }

    /// Returns the device configuration.
    #[must_use]
    pub fn device(&self) -> &Device {
        &self.device
    }

    /// Returns the starting frame index of the next cycle.
    #[must_use]
    pub fn position(&self) -> u64 {
        self.position
    }

    /// Returns the host-clock timestamp (ns) when the next capture cycle is
    /// delivered (`reported(end) + lead`).
    #[must_use]
    pub fn due(&self) -> i64 {
        let end = self.position.saturating_add(self.device.cycle as u64);
        self.device.reported(end).saturating_add(self.device.lead)
    }

    /// Generates one cycle of frames and delivers it to `capture` if its
    /// channel count matches `self.device.channels`.
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

    /// Runs all capture cycles due at or before host-clock timestamp `now` (ns)
    /// and returns the number of cycles executed.
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

    /// Test playback sink that tags each frame with its index and logs cycle metadata.
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

    #[test]
    fn reported_timestamps_follow_device_rate_and_drift() {
        // At 50 kHz each frame is exactly 20,000 ns.
        let exact = device();
        assert_eq!(exact.reported(0), 1_000_000);
        assert_eq!(exact.reported(50_000), 1_001_000_000);
        // +1,000 ppm (+1,000,000 ppb) plays 50,050 frames per second.
        let fast = Device {
            drift: 1_000_000,
            ..exact
        };
        assert_eq!(fast.reported(50_050), 1_001_000_000);
        // Floor division avoids cumulative rounding drift.
        let slow = Device { rate: 3, ..exact };
        assert_eq!(slow.reported(1), 1_000_000 + 333_333_333);
        assert_eq!(slow.reported(3), 1_001_000_000);
    }

    #[test]
    fn hidden_latency_shifts_true_times_only() {
        let hiding = Device {
            hidden: 250_000,
            ..device()
        };
        assert_eq!(hiding.reported(100), device().reported(100));
        assert_eq!(hiding.played(100), hiding.reported(100) + 250_000);
        assert_eq!(hiding.captured(100), hiding.reported(100) - 250_000);
    }

    #[test]
    fn output_schedules_cycles_by_lead_time() {
        let mut output = Output::new(device(), 250);
        let mut playback = Counting { cycles: Vec::new() };
        // Cycle 0 plays at 1 ms and is requested at -2 ms; subsequent cycles step by 2 ms.
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
    fn output_records_up_to_capacity_and_counts_overflow() {
        let mut output = Output::new(device(), 250);
        let mut playback = Counting { cycles: Vec::new() };
        assert_eq!(output.run(3_999_999, &mut playback), 3);
        // Capacity of 250 frames fits two 100-frame cycles; the third is counted as unrecorded.
        let recorded = output.recorded();
        assert_eq!(recorded.len(), 400);
        assert_eq!(recorded[0..2], [0.0, -1.0]);
        assert_eq!(recorded[398..400], [199.0, -1.0]);
        assert_eq!(output.unrecorded(), 100);
    }

    /// Test capture sink that logs received cycles and sample data.
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
    fn input_delivers_cycles_after_capture_plus_lead() {
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
        // Cycle 0 finishes capturing at 3 ms and is delivered at 3 ms + 3 ms lead = 6 ms.
        assert_eq!(input.due(), 6_000_000);
        assert_eq!(input.run(5_999_999, &mut capture), 0);
        assert_eq!(input.run(8_000_000, &mut capture), 2);
        assert_eq!(capture.cycles, [(0, 1_000_000), (100, 3_000_000)]);
        assert_eq!(capture.frames.len(), 400);
        assert_eq!(capture.frames[198..202], [0.5, 0.25, 0.5, -0.25]);
        drop(input);
        // True capture time precedes the reported timestamp by `hidden` (250 us).
        assert_eq!(times, [750_000, 770_000]);
    }

    #[test]
    fn zero_cycle_device_does_not_run() {
        let none = Device {
            cycle: 0,
            ..device()
        };
        let mut output = Output::new(none, 10);
        let mut playback = Counting { cycles: Vec::new() };
        assert_eq!(output.run(i64::MAX, &mut playback), 0);
    }
}
