// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The resampler that corrects clock drift.

use crate::filter::Filter;
use crate::position::{Position, Step};

/// A run of consecutive frames of a stream, with the channels of each frame
/// side by side.
#[derive(Clone, Copy, Debug)]
pub struct Window<'a> {
    /// The index of the first frame in `samples`.
    pub first: u64,
    /// The samples, frame after frame. Samples beyond the last whole frame
    /// are not used.
    pub samples: &'a [f32],
}

/// What a call of [`Resampler::process`] wrote.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Produced {
    /// The number of frames written.
    pub frames: usize,
    /// The position that the next frame would be taken at.
    pub next: Position,
}

/// Computes the frames of a stream at positions that the caller chooses.
///
/// It keeps no samples and no position between calls. Each output frame is a
/// function of the window, the position and nothing else, so the same
/// positions give the same output however the work is cut into calls, and a
/// jump is a call with another position.
#[derive(Clone, Debug)]
pub struct Resampler {
    filter: Filter,
    channels: usize,
    row: Box<[f32]>,
}

impl Resampler {
    /// A resampler for frames of `channels` samples.
    #[must_use]
    pub fn new(filter: Filter, channels: usize) -> Resampler {
        let row = vec![0.0; filter.taps()].into_boxed_slice();
        Resampler {
            filter,
            channels,
            row,
        }
    }

    /// The filter that gives the value between frames.
    #[must_use]
    pub fn filter(&self) -> &Filter {
        &self.filter
    }

    /// The number of samples in a frame.
    #[must_use]
    pub fn channels(&self) -> usize {
        self.channels
    }

    /// Writes into `output` the stream's frames at the positions `start`,
    /// `start + step`, `start + 2 * step` and so on, exactly: output frame
    /// `i` is taken at `start.advance(step, i)`.
    ///
    /// The frame at a position `p` whose last whole frame is `n` is computed
    /// from the frames `n - filter().before()` to `n + filter().ahead()` of
    /// the stream, weighted symmetrically about `p`, so it is not delayed
    /// with respect to `p`. Writing stops before the first output frame that
    /// needs a frame outside `window`, at the end of `output`, and at the
    /// largest position. Nothing outside `window` is read.
    pub fn process(
        &mut self,
        window: Window<'_>,
        start: Position,
        step: Step,
        output: &mut [f32],
    ) -> Produced {
        let mut produced = Produced {
            frames: 0,
            next: start,
        };
        if self.channels == 0 {
            return produced;
        }
        let taps = self.filter.taps();
        let before = self.filter.before() as u64;
        let held = window.samples.len() / self.channels;
        let step = step.units();
        let mut position = start.units();
        for frame in output.chunks_exact_mut(self.channels) {
            let at = Position::from_units(position);
            // The first frame that this position needs, counted from the
            // start of the window.
            let Some(from) = at
                .frame()
                .checked_sub(before)
                .and_then(|needed| needed.checked_sub(window.first))
                .and_then(|from| usize::try_from(from).ok())
            else {
                break;
            };
            let Some(end) = from.checked_add(taps).filter(|end| *end <= held) else {
                break;
            };
            let Some(needed) = window
                .samples
                .get(from * self.channels..end * self.channels)
            else {
                break;
            };
            let Some(next) = position.checked_add(step) else {
                break;
            };
            self.filter.coefficients(at.fraction(), &mut self.row);
            for (channel, sample) in frame.iter_mut().enumerate() {
                // The sum is taken in double precision and rounded once, so
                // its error is that of one rounding to an f32.
                let mut sum = 0.0f64;
                let samples = needed.iter().skip(channel).step_by(self.channels);
                for (weight, sample) in self.row.iter().zip(samples) {
                    sum += f64::from(*weight) * f64::from(*sample);
                }
                #[allow(clippy::cast_possible_truncation)] // rounding to f32 is intended
                let value = sum as f32;
                *sample = value;
            }
            position = next;
            produced.frames += 1;
        }
        produced.next = Position::from_units(position);
        produced
    }
}
