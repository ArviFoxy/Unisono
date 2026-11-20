// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The concealment of gaps against sounds whose continuation is known.

#![allow(clippy::cast_precision_loss)] // frame indices as f64
#![allow(clippy::cast_possible_truncation)] // test signals are rounded to f32 on purpose

use std::f64::consts::PI;

use unisono_dsp::{Concealment, Fade, Parameters};

const RATE: u32 = 48_000;

/// A sinusoid of `hertz` and the given amplitude at frame `frame`.
fn tone(hertz: f64, amplitude: f64, frame: usize) -> f64 {
    amplitude * (2.0 * PI * hertz * frame as f64 / f64::from(RATE) + 0.3).sin()
}

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
        (self.next() as f64 / 2f64.powi(30) - 1.0) as f32
    }
}

fn bits(samples: &[f32]) -> Vec<u32> {
    samples.iter().map(|sample| sample.to_bits()).collect()
}

/// Detects a wrong shape or length of a fade: the gains must rise without a
/// step back, strictly inside zero to one for exactly the frames of the
/// fade, and the falling gain must be what the rising gain lacks to one.
#[test]
fn a_fade_is_a_raised_cosine_of_its_length() {
    for frames in [1usize, 2, 240, 960] {
        let fade = Fade::new(frames);
        assert_eq!(fade.frames(), frames);
        let mut last = 0.0f32;
        for frame in 0..frames {
            let rising = fade.rising(frame);
            let expected = (PI * (frame as f64 + 1.0) / (2.0 * (frames as f64 + 1.0)))
                .sin()
                .powi(2);
            assert!((f64::from(rising) - expected).abs() < 1e-7, "frame {frame}");
            assert!(rising > last && rising < 1.0, "frame {frame} of {frames}");
            assert!((rising + fade.falling(frame) - 1.0).abs() < 2e-7);
            last = rising;
        }
        for frame in [frames, frames + 1, usize::MAX] {
            assert_eq!(fade.rising(frame).to_bits(), 1.0f32.to_bits());
            assert_eq!(fade.falling(frame).to_bits(), 0.0f32.to_bits());
        }
    }
    let none = Fade::new(0);
    assert_eq!((none.rising(0), none.falling(0)), (1.0, 0.0));
}

/// The first frames of a stream, and the frames after a long gap, must rise
/// by the fade in from silence, and then be left exactly as they are.
#[test]
fn a_stream_fades_in_from_silence() {
    let parameters = Parameters::for_rate(RATE);
    assert_eq!(
        parameters,
        Parameters {
            fitted: 480,
            order: 32,
            fade_out: 960,
            fade_in: 240
        }
    );
    let mut concealment = Concealment::new(1, parameters);
    let mut random = Random(1);
    for round in 0..2 {
        let input: Vec<f32> = (0..400).map(|_| random.sample()).collect();
        let mut frames = input.clone();
        concealment.pass(&mut frames);
        for (index, (output, input)) in frames.iter().zip(&input).enumerate() {
            let expected = concealment.fade_in().rising(index) * input;
            assert_eq!(
                output.to_bits(),
                expected.to_bits(),
                "round {round}, frame {index}"
            );
        }
        // A gap longer than the fade out, which ends in silence.
        let mut gap = vec![1.0f32; 1500];
        concealment.fill(&mut gap);
        assert!(gap[960..].iter().all(|sample| sample.to_bits() == 0));
    }
}

/// Detects a prediction that is fitted or run wrongly: weights applied to
/// the wrong samples, or a model whose sign or order is wrong, continue a
/// tone with an error as large as the tone. The continuation of a steady
/// tone is the tone, times the fade out from the start of the gap. The
/// bounds are the documented accuracy: 3 % of the amplitude over the first
/// millisecond and 15 % over the first two, for tones from 50 Hz up.
#[test]
fn a_steady_tone_is_continued_with_the_documented_accuracy() {
    for step in 0..60 {
        let hertz = 50.0 * 400f64.powf(f64::from(step) / 59.0);
        for phase in 0..4 {
            let shift = phase * 331;
            let mut frames: Vec<f32> = (0..1000)
                .map(|frame| tone(hertz, 0.5, frame + shift) as f32)
                .collect();
            let mut concealment = Concealment::new(1, Parameters::for_rate(RATE));
            concealment.pass(&mut frames);
            let mut gap = [f32::NAN; 96];
            concealment.fill(&mut gap);
            for (age, sample) in gap.iter().enumerate() {
                let fade = f64::from(concealment.fade_out().falling(age))
                    / f64::from(concealment.fade_out().falling(0));
                let expected = fade * tone(hertz, 0.5, 1000 + shift + age);
                let error = (f64::from(*sample) - expected).abs() / 0.5;
                let bound = if age < 48 { 0.03 } else { 0.15 };
                assert!(
                    error <= bound,
                    "{hertz:.1} Hz, phase {phase}, frame {age} of the gap: {error:.4}"
                );
            }
        }
    }
}

/// Detects frames that are changed when they should not be, channels that
/// are mixed up, and a gap whose frames are not all written: outside the
/// gap and the fades the output must be the input bit for bit, and across
/// the gap each channel must carry its own tone on.
#[test]
fn only_the_gap_and_the_fade_in_after_it_differ_from_the_stream() {
    let (before, gap, after) = (2400, 96, 600);
    let (left, right) = ((997.0, 0.5), (3_011.0, 0.25));
    let mut frames: Vec<f32> = (0..before + gap + after)
        .flat_map(|frame| {
            [
                tone(left.0, left.1, frame) as f32,
                tone(right.0, right.1, frame) as f32,
            ]
        })
        .collect();
    let input = frames.clone();
    let mut concealment = Concealment::new(2, Parameters::for_rate(RATE));
    let (head, rest) = frames.split_at_mut(2 * before);
    let (missing, tail) = rest.split_at_mut(2 * gap);
    concealment.pass(head);
    missing.fill(f32::NAN);
    concealment.fill(missing);
    concealment.pass(tail);

    let unchanged = |frames: std::ops::Range<usize>| 2 * frames.start..2 * frames.end;
    assert_eq!(
        bits(&frames[unchanged(240..before)]),
        bits(&input[unchanged(240..before)])
    );
    let rest = before + gap + 240..before + gap + after;
    assert_eq!(
        bits(&frames[unchanged(rest.clone())]),
        bits(&input[unchanged(rest)])
    );
    for (age, frame) in frames[unchanged(before..before + gap)]
        .as_chunks::<2>()
        .0
        .iter()
        .enumerate()
    {
        let fade = f64::from(concealment.fade_out().falling(age))
            / f64::from(concealment.fade_out().falling(0));
        for (sample, (hertz, amplitude)) in [(frame[0], left), (frame[1], right)] {
            let error = (f64::from(sample) - fade * tone(hertz, amplitude, before + age)).abs();
            assert!(
                error <= 0.15 * amplitude,
                "{hertz} Hz, frame {age} of the gap"
            );
        }
    }
}

/// Detects a fade in that is mixed wrongly with the continuation, or a
/// continuation that stops or restarts when frames arrive. When silence
/// arrives after a gap, what is heard is only the continuation: the same
/// samples that a longer gap would have given, times what the fade in
/// leaves of them.
#[test]
fn the_continuation_goes_on_under_the_fade_in() {
    let lead: Vec<f32> = (0..2000)
        .map(|frame| tone(440.0, 0.5, frame) as f32)
        .collect();
    let mut longer_gap = Concealment::new(1, Parameters::for_rate(RATE));
    let mut silence_arrives = Concealment::new(1, Parameters::for_rate(RATE));
    let mut continued = [0.0f32; 96 + 400];
    let mut mixed = [0.0f32; 96 + 400];
    longer_gap.pass(&mut lead.clone());
    silence_arrives.pass(&mut lead.clone());
    longer_gap.fill(&mut continued);
    silence_arrives.fill(&mut mixed[..96]);
    silence_arrives.pass(&mut mixed[96..]);

    assert_eq!(bits(&mixed[..96]), bits(&continued[..96]));
    for (frame, (mixed, continued)) in mixed[96..].iter().zip(&continued[96..]).enumerate() {
        let left_by_fade_in = 1.0 - silence_arrives.fade_in().rising(frame);
        assert!(
            (mixed - left_by_fade_in * continued).abs() <= 1e-6,
            "frame {frame} after the gap"
        );
    }
    // The comparison is not between two silences.
    assert!(continued[96..200].iter().any(|sample| sample.abs() > 0.3));
    assert!(mixed[96 + 240..].iter().all(|sample| sample.to_bits() == 0));
}

/// A sound, as its sample at each frame.
type Sound = Box<dyn FnMut(usize) -> f64>;

/// Detects a continuation that grows beyond the sound it continues, which
/// could be loud. Each of these sounds leads a prediction astray: noise,
/// which cannot be predicted; a sound that is growing; a sound whose slow
/// swell has only begun in the fitted frames, so that its true continuation
/// is louder than anything fitted; and single spikes.
#[test]
fn a_continuation_is_never_louder_than_the_sound_before_it() {
    let mut random = Random(9);
    let sounds: [(&str, Sound); 4] = [
        ("noise", Box::new(move |_| 0.3 * f64::from(random.sample()))),
        (
            "growing",
            Box::new(|frame| 0.5 * 1.01f64.powf(frame as f64 - 4799.0) * tone(700.0, 1.0, frame)),
        ),
        (
            "swell",
            Box::new(|frame| {
                (0..5)
                    .map(|partial| tone(60.0 * (1.0 + 0.37 * f64::from(partial)), 0.1, frame + 77))
                    .sum()
            }),
        ),
        (
            "spikes",
            Box::new(|frame| if frame % 97 == 0 { 0.9 } else { 0.0 }),
        ),
    ];
    for (name, mut sound) in sounds {
        let mut frames: Vec<f32> = (0..4800).map(|frame| sound(frame) as f32).collect();
        let mut concealment = Concealment::new(1, Parameters::for_rate(RATE));
        concealment.pass(&mut frames);
        let peak = frames[4800 - 480..]
            .iter()
            .fold(0.0f32, |peak, sample| peak.max(sample.abs()));
        let mut gap = vec![0.0f32; 1000];
        concealment.fill(&mut gap);
        let loudest = gap
            .iter()
            .fold(0.0f32, |peak, sample| peak.max(sample.abs()));
        assert!(loudest <= peak, "{name}: {loudest} after a peak of {peak}");
        assert!(gap.iter().all(|sample| sample.is_finite()));
    }
}

/// Detects a sound that is kept alive by gaps that follow each other
/// closely: each gap would otherwise continue, at full level, a sound that
/// is itself mostly the last gap's continuation.
///
/// Here one frame of silence arrives between gaps of 47 frames. A gap
/// enters the fade out at the place the last one had reached, times the
/// share of the fade in that was missing, 239 of 240. The test follows that
/// rule in whole numbers until the fade out has been used up, and from the
/// gap after that the output must be silence exactly.
#[test]
fn gaps_in_quick_succession_do_not_keep_a_sound_alive() {
    let parameters = Parameters::for_rate(RATE);
    let mut concealment = Concealment::new(1, parameters);
    let mut frames: Vec<f32> = (0..4800)
        .map(|frame| tone(440.0, 0.5, frame) as f32)
        .collect();
    concealment.pass(&mut frames);

    let mut age = 0;
    let mut rounds_until_silence = 0;
    while age < parameters.fade_out {
        // 47 missing frames and one that arrives, then the next gap begins.
        age = (age + 48).min(parameters.fade_out) * 239 / 240;
        rounds_until_silence += 1;
        assert!(rounds_until_silence < 1000, "the fade out is never used up");
        if (age + 48).min(parameters.fade_out) == parameters.fade_out {
            break;
        }
    }
    let mut energy_early = 0.0f64;
    for round in 0..rounds_until_silence + 20 {
        let mut gap = [0.0f32; 47];
        concealment.fill(&mut gap);
        let mut arrived = [0.0f32];
        concealment.pass(&mut arrived);
        if round == 0 {
            energy_early = gap.iter().map(|sample| f64::from(*sample).powi(2)).sum();
        }
        if round > rounds_until_silence + 1 {
            assert!(
                gap.iter()
                    .chain(&arrived)
                    .all(|sample| sample.to_bits() == 0),
                "round {round}"
            );
        }
    }
    // The first gap did carry the tone on: 47 frames at about half a
    // squared amplitude of 0.25 each.
    assert!(energy_early > 0.8 * 47.0 * 0.125, "{energy_early}");
}

/// Detects state that depends on how the frames were grouped into calls:
/// a gap that is begun again at every call, or a fade that restarts.
#[test]
fn the_output_does_not_depend_on_how_frames_are_grouped_into_calls() {
    let channels = 2;
    let mut random = Random(4);
    // Runs of frames that arrive and that are missing, of 1 to 400 frames.
    let runs: Vec<(bool, usize)> = (0..120)
        .map(|run| (run % 2 == 0, random.next() as usize % 400 + 1))
        .collect();
    let total: usize = runs.iter().map(|(_, frames)| frames).sum();
    let input: Vec<f32> = (0..total)
        .flat_map(|frame| {
            [
                (tone(523.0, 0.4, frame) + 0.05 * f64::from(random.sample())) as f32,
                random.sample() * 0.2,
            ]
        })
        .collect();

    let mut whole = input.clone();
    let mut pieces = input.clone();
    let mut in_runs = Concealment::new(channels, Parameters::for_rate(RATE));
    let mut in_pieces = Concealment::new(channels, Parameters::for_rate(RATE));
    let mut start = 0;
    for (arrived, frames) in runs {
        let run = start * channels..(start + frames) * channels;
        if arrived {
            in_runs.pass(&mut whole[run.clone()]);
        } else {
            in_runs.fill(&mut whole[run.clone()]);
        }
        let mut done = 0;
        while done < frames {
            let piece = (random.next() as usize % 64).min(frames - done);
            let from = (start + done) * channels;
            let samples = &mut pieces[from..from + piece * channels];
            if arrived {
                in_pieces.pass(samples);
            } else {
                in_pieces.fill(samples);
            }
            done += piece;
        }
        start += frames;
    }
    assert_eq!(bits(&whole), bits(&pieces));
    // The gaps were filled with something: the test is not about silence.
    assert_ne!(bits(&whole), bits(&input));
}

/// Inputs at the edges of what the types allow must not fail, and frames
/// that are not numbers must not spoil a later gap.
#[test]
fn degenerate_sizes_and_frames_that_are_not_numbers_do_no_harm() {
    let mut frames = [0.5f32; 64];
    Concealment::new(0, Parameters::for_rate(RATE)).pass(&mut frames);
    Concealment::new(0, Parameters::for_rate(RATE)).fill(&mut frames);
    assert_eq!(bits(&frames), bits(&[0.5; 64]));

    // No prediction at all: gaps are silence, and the stream still fades in.
    let fades_only = Parameters {
        fitted: 0,
        order: 7,
        fade_out: 10,
        fade_in: 4,
    };
    let mut concealment = Concealment::new(2, fades_only);
    assert_eq!(concealment.parameters().order, 0);
    concealment.pass(&mut frames);
    assert_eq!(frames[8..], [0.5; 56]);
    concealment.fill(&mut frames);
    assert_eq!(bits(&frames), bits(&[0.0; 64]));

    let huge = Parameters {
        fitted: usize::MAX,
        order: usize::MAX,
        fade_out: usize::MAX,
        fade_in: usize::MAX,
    };
    assert_eq!(
        huge.within_limits(),
        Parameters {
            fitted: 1 << 14,
            order: 256,
            fade_out: 1 << 20,
            fade_in: 1 << 20
        }
    );

    let mut concealment = Concealment::new(1, Parameters::for_rate(RATE));
    let mut spoiled = [f32::NAN; 600];
    concealment.pass(&mut spoiled);
    let mut gap = [1.0f32; 100];
    concealment.fill(&mut gap);
    assert!(gap.iter().all(|sample| sample.is_finite()));
    let mut frames: Vec<f32> = (0..2000)
        .map(|frame| tone(440.0, 0.5, frame) as f32)
        .collect();
    concealment.pass(&mut frames);
    concealment.fill(&mut gap);
    // The tone is continued again: about half a squared amplitude a frame.
    let energy: f64 = gap.iter().map(|sample| f64::from(*sample).powi(2)).sum();
    assert!(energy > 0.8 * 100.0 * 0.125, "{energy}");
}
