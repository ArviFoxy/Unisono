// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The resampler against sinusoids whose value at any position is known,
//! and against the exact arithmetic of its positions.

#![allow(clippy::cast_precision_loss)] // frame indices and 64-bit fractions as f64

use std::f64::consts::PI;

use unisono_dsp::{Filter, Position, Produced, Resampler, Step, Window};

/// Numbers that are the same on every run.
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    /// A sample between -1 and 1.
    fn sample(&mut self) -> f32 {
        #[allow(clippy::cast_possible_truncation)]
        let value = (self.next() as f64 / 2f64.powi(30) - 1.0) as f32;
        value
    }
}

fn as_number(position: Position) -> f64 {
    position.frame() as f64 + position.fraction() as f64 / 2f64.powi(64)
}

/// A sinusoid of `cycles` cycles per frame, shifted by `phase`, at frame or
/// position `at`.
fn sinusoid(cycles: f64, phase: f64, at: f64) -> f64 {
    (2.0 * PI * cycles * at + phase).sin()
}

/// Detects a wrong weight, a weight applied to the wrong frame, a position
/// that is off by a fraction of a frame, and channels that are mixed up: any
/// of them moves the output away from the sinusoid's true value at the
/// position by far more than the bound.
///
/// The bound is the error the filter is designed for, plus what rounding the
/// input and the output to single precision can add: the input is rounded by
/// at most 2^-25 a sample, which the weights (whose sizes add up to less
/// than 4) pass on as at most 1.2e-7, and the output by at most 6e-8.
#[test]
fn a_sinusoid_comes_out_at_its_true_value_at_every_position() {
    #![allow(clippy::cast_possible_truncation)] // the test signal is rounded to f32 on purpose
    let bound = 10f64.powf(-Filter::ERROR_DECIBELS / 20.0) + 2e-7;
    for rate in [44_100u32, 48_000] {
        let mut resampler = Resampler::new(Filter::for_rate(rate), 2);
        let before = resampler.filter().before() as u64;
        for hertz in [50.0, 997.0, 10_007.0, 19_001.0, 20_000.0] {
            let left = hertz / f64::from(rate);
            // The other channel carries another sinusoid.
            let right = left * 0.37;
            let input: Vec<f32> = (0..3000)
                .flat_map(|frame| {
                    let at = f64::from(frame);
                    [
                        sinusoid(left, 0.4, at) as f32,
                        sinusoid(right, 1.9, at) as f32,
                    ]
                })
                .collect();
            let window = Window {
                first: 0,
                samples: &input,
            };
            for parts in [-1_000_000i64, -300_000, -1, 0, 1, 300_000, 1_000_000] {
                let step = Step::from_parts_per_billion(parts);
                let start = Position::new(before + 3, 0x4ccc_cccc_cccc_cccd);
                let mut output = vec![0.0f32; 2 * 2800];
                let produced = resampler.process(window, start, step, &mut output);
                assert_eq!(produced.frames, 2800);
                for (index, frame) in output.as_chunks::<2>().0.iter().enumerate() {
                    let at = as_number(start.advance(step, index as u64).expect("in range"));
                    for (sample, cycles, phase) in [(frame[0], left, 0.4), (frame[1], right, 1.9)] {
                        let error = (f64::from(sample) - sinusoid(cycles, phase, at)).abs();
                        assert!(
                            error <= bound,
                            "{rate} frames per second, {hertz} Hz, {parts} parts per \
                             billion, output frame {index}: error {error:e}"
                        );
                    }
                }
            }
        }
    }
}

/// Detects any rounding in the positions: the position after a call must be
/// the position before it plus the number of frames times the step, in whole
/// numbers of 2^-64 frame, over millions of calls with changing steps and
/// block sizes.
#[test]
fn positions_add_up_exactly_over_millions_of_calls() {
    // A short filter, because this test is about positions and not values.
    let mut resampler = Resampler::new(Filter::kaiser(8, 5.0, 4), 1);
    let before = resampler.filter().before() as u64;
    let input = [0.25f32; 24];
    let mut output = [0.0f32; 8];
    let mut random = Random(11);
    let mut position = Position::new(before, 1);
    // The same position as a count of units of 2^-64 frame, kept separately.
    let mut units = (u128::from(before) << 64) + 1;
    let mut step = Step::UNITY;
    for call in 0..2_000_000u32 {
        if call % 1000 == 0 {
            let parts = i64::try_from(random.next() % 2_000_001).expect("small") - 1_000_000;
            step = Step::from_parts_per_billion(parts);
        }
        let frames = usize::try_from(random.next() % 8).expect("small") + 1;
        let window = Window {
            first: position.frame() - before,
            samples: &input,
        };
        let produced = resampler.process(window, position, step, &mut output[..frames]);
        let advance = ((1i128 << 64) + i128::from(step.offset())) * frames as i128;
        units += u128::try_from(advance).expect("positive");
        let expected = Position::new(
            u64::try_from(units >> 64).expect("in range"),
            u64::try_from(units & u128::from(u64::MAX)).expect("in range"),
        );
        assert_eq!(
            produced,
            Produced {
                frames,
                next: expected
            },
            "call {call}"
        );
        position = produced.next;
    }
    // About nine million frames have passed; the last frame's value is still
    // that of the constant input, so the values were taken where the
    // positions say.
    assert!((output[0] - 0.25).abs() < 1e-6);
}

fn noise(frames: usize, channels: usize) -> Vec<f32> {
    let mut random = Random(5);
    (0..frames * channels).map(|_| random.sample()).collect()
}

/// Detects state that is carried from one call to the next, and any
/// dependence on where the window starts: the same positions must give the
/// same output, bit for bit, in one call or in many calls of varying length,
/// each with a window that holds only the frames it needs.
#[test]
fn the_output_does_not_depend_on_how_the_work_is_cut_into_calls() {
    let channels = 2;
    let mut resampler = Resampler::new(Filter::for_rate(48_000), channels);
    let (before, ahead) = (
        resampler.filter().before() as u64,
        resampler.filter().ahead() as u64,
    );
    let input = noise(5000, channels);
    let step = Step::from_parts_per_billion(777_123);
    let start = Position::new(before + 10, 0x8123_4567_89ab_cdef);
    let total = 4500;
    let mut whole = vec![0.0f32; total * channels];
    let window = Window {
        first: 0,
        samples: &input,
    };
    assert_eq!(
        resampler.process(window, start, step, &mut whole).frames,
        total
    );

    let mut pieces = vec![0.0f32; total * channels];
    let mut random = Random(3);
    let mut done = 0;
    let mut position = start;
    while done < total {
        let frames = (usize::try_from(random.next() % 97).expect("small") + 1).min(total - done);
        let last = position.advance(step, frames as u64 - 1).expect("in range");
        let first_needed = usize::try_from(position.frame() - before).expect("small");
        let last_needed = usize::try_from(last.frame() + ahead).expect("small");
        let window = Window {
            first: first_needed as u64,
            samples: &input[first_needed * channels..(last_needed + 1) * channels],
        };
        let produced = resampler.process(
            window,
            position,
            step,
            &mut pieces[done * channels..(done + frames) * channels],
        );
        assert_eq!(produced.frames, frames);
        position = produced.next;
        done += frames;
    }
    let bits = |samples: &[f32]| {
        samples
            .iter()
            .map(|sample| sample.to_bits())
            .collect::<Vec<_>>()
    };
    assert_eq!(bits(&whole), bits(&pieces));
    assert_eq!(Some(position), start.advance(step, total as u64));
}

/// A stream that is played at its own rate and on its own frames must come
/// out unchanged, bit for bit.
#[test]
fn a_step_of_one_on_whole_frames_returns_the_input() {
    let channels = 3;
    let mut resampler = Resampler::new(Filter::for_rate(44_100), channels);
    let before = resampler.filter().before();
    let ahead = resampler.filter().ahead();
    let input = noise(400, channels);
    let window = Window {
        first: 7000,
        samples: &input,
    };
    let mut output = vec![0.0f32; 1000 * channels];
    let start = Position::at_frame(7000 + before as u64);
    let produced = resampler.process(window, start, Step::UNITY, &mut output);
    // The last position whose frames are all there is `ahead` frames before
    // the end of the window: that is the delay of the filter.
    let frames = 400 - before - ahead;
    assert_eq!(
        produced,
        Produced {
            frames,
            next: Position::at_frame(7000 + (before + frames) as u64)
        }
    );
    let expected = &input[before * channels..(before + frames) * channels];
    let bits = |samples: &[f32]| {
        samples
            .iter()
            .map(|sample| sample.to_bits())
            .collect::<Vec<_>>()
    };
    assert_eq!(bits(&output[..frames * channels]), bits(expected));
}

/// Detects an offset of the weights by one frame, and a read outside the
/// frames a position is said to need. A frame that is not a number spoils
/// every value it takes part in, so it shows which frames a value was
/// computed from.
#[test]
fn a_value_is_computed_from_exactly_the_frames_it_is_said_to_need() {
    let mut resampler = Resampler::new(Filter::for_rate(48_000), 1);
    let before = resampler.filter().before();
    let ahead = resampler.filter().ahead();
    let at = 200;
    let value_with_gap_at = |resampler: &mut Resampler, spoiled: usize| {
        let mut input = vec![0.5f32; 400];
        input[spoiled] = f32::NAN;
        let window = Window {
            first: 0,
            samples: &input,
        };
        let mut output = [0.0f32];
        let start = Position::new(at as u64, 1 << 63);
        assert_eq!(
            resampler
                .process(window, start, Step::UNITY, &mut output)
                .frames,
            1
        );
        output[0]
    };
    assert!(value_with_gap_at(&mut resampler, at - before).is_nan());
    assert!(value_with_gap_at(&mut resampler, at + ahead).is_nan());
    assert!(value_with_gap_at(&mut resampler, at - before - 1).is_finite());
    assert!(value_with_gap_at(&mut resampler, at + ahead + 1).is_finite());
}

/// Detects a position being served from frames that the window does not
/// hold: whatever position a call starts at, it writes exactly the frames
/// whose needed frames lie in the window, and none when the first does not.
#[test]
fn a_call_at_any_position_writes_only_what_the_window_allows() {
    let mut resampler = Resampler::new(Filter::for_rate(48_000), 1);
    let before = resampler.filter().before() as u64;
    let ahead = resampler.filter().ahead() as u64;
    let input = noise(300, 1);
    let window = Window {
        first: 1000,
        samples: &input,
    };
    let (first_possible, last_possible) = (1000 + before, 1299 - ahead);
    let step = Step::from_parts_per_billion(1_000_000);
    let mut output = vec![0.0f32; 1000];
    for start in [
        Position::at_frame(0),
        Position::new(first_possible - 1, u64::MAX),
        Position::at_frame(first_possible),
        Position::new(first_possible + 100, 12345),
        Position::new(last_possible, u64::MAX),
        Position::at_frame(last_possible + 1),
        Position::at_frame(5000),
        Position::new(u64::MAX, u64::MAX),
    ] {
        let mut expected = 0;
        if start.frame() >= first_possible {
            while start
                .advance(step, expected)
                .is_some_and(|position| position.frame() <= last_possible)
            {
                expected += 1;
            }
        }
        let produced = resampler.process(window, start, step, &mut output);
        assert_eq!(produced.frames as u64, expected, "start {start:?}");
        assert_eq!(Some(produced.next), start.advance(step, expected));
    }
}

/// Inputs at the edges of what the types allow must give no output and no
/// failure.
#[test]
fn degenerate_calls_write_nothing() {
    let input = noise(100, 2);
    let window = Window {
        first: 0,
        samples: &input,
    };
    let start = Position::at_frame(50);
    let nothing = Produced {
        frames: 0,
        next: start,
    };
    let mut output = [0.0f32; 16];

    let mut no_channels = Resampler::new(Filter::for_rate(48_000), 0);
    assert_eq!(
        no_channels.process(window, start, Step::UNITY, &mut output),
        nothing
    );

    let mut resampler = Resampler::new(Filter::for_rate(48_000), 2);
    assert_eq!(
        resampler.process(window, start, Step::UNITY, &mut []),
        nothing
    );
    // Less than one frame of output.
    assert_eq!(
        resampler.process(window, start, Step::UNITY, &mut output[..1]),
        nothing
    );
    let empty = Window {
        first: 50,
        samples: &[],
    };
    assert_eq!(
        resampler.process(empty, start, Step::UNITY, &mut output),
        nothing
    );
    let far = Window {
        first: u64::MAX,
        samples: &input,
    };
    let last = Position::new(u64::MAX, u64::MAX);
    assert_eq!(
        resampler.process(far, last, Step::UNITY, &mut output),
        Produced {
            frames: 0,
            next: last
        }
    );
    // 48 frames and one sample more, which is not part of a frame.
    let odd = Window {
        first: 0,
        samples: &input[..97],
    };
    let produced = resampler.process(odd, Position::at_frame(23), Step::UNITY, &mut output);
    assert_eq!(produced.frames, 1);
}
