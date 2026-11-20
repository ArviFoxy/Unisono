// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A stream through a receiver, its store and its pump into a software
//! device.
//!
//! Most tests run a scene in which every time is a whole number of frames:
//! 50,000 frames a second, so that a frame lasts 20,000 nanoseconds, clocks
//! that differ by a constant, and a device exactly at its rate. Every
//! position that the receiver plays is then a whole frame, the resampler
//! returns frames as they are, and with fades of no length every output
//! sample is a sample of the stream or silence. The stream is a ramp, in
//! which a sample says which frame it is, so each output frame can be held
//! against the frame that is due when it leaves the device.
//!
//! The last tests run a device and clocks that drift, where the output is
//! the stream between its frames.

// The scene in whole frames is made so that samples are exact, and they are
// compared exactly.
#![allow(clippy::float_cmp)]

mod common;

use std::f64::consts::TAU;

use common::{CHANNELS, Line, Listener, index_of, no_fades, ramp, run, settings};
use unisono_core::sender::Sender;
use unisono_dsp::{Filter, Parameters};
use unisono_runtime::pump::Totals;
use unisono_runtime::software::{Device, Output};

/// Frames per second, frames in a packet, and the latency in nanoseconds
/// and in frames, of the scene in whole frames.
const RATE: u32 = 50_000;
const PACKET: u16 = 250;
const LEVEL: i64 = 30_000_000;
const LEVEL_FRAMES: u64 = 1_500;

/// What a run of the scene in whole frames gave.
struct Outcome {
    /// The first channel of every frame the device played, by the device's
    /// count.
    first: Vec<f32>,
    /// The second channel.
    second: Vec<f32>,
    totals: Totals,
}

/// What varies between the runs of the scene in whole frames.
struct Scene {
    /// Frames in a cycle of the device.
    cycle: usize,
    concealment: Parameters,
    /// The numbers of the packets that do not arrive.
    lost: Vec<u64>,
    /// With the packet of the first number arrives a copy of the packet of
    /// the second.
    repeated: Vec<(u64, u64)>,
    /// The distance, in frames, beyond which the receiver jumps.
    jump: u32,
}

/// The scene with a cycle of 250 frames, fades of no length and a jump
/// beyond 240 frames.
fn scene() -> Scene {
    Scene {
        cycle: 250,
        concealment: no_fades(),
        lost: Vec::new(),
        repeated: Vec::new(),
        jump: 240,
    }
}

/// Runs the scene in whole frames for a second.
///
/// The device's frame 0 leaves when the sender's clock reads 0, so the
/// device's frame `p` is due to be the stream's frame `p - LEVEL_FRAMES` as
/// long as the level is `LEVEL`.
fn whole_frames(scene: &Scene, before: impl FnMut(u64, &mut Sender)) -> Outcome {
    let mut line = Line::new(RATE, PACKET, LEVEL, ramp);
    line.lost.clone_from(&scene.lost);
    line.repeated.clone_from(&scene.repeated);
    let mut listener_settings = settings(RATE, scene.concealment);
    listener_settings.regulation.jump = scene.jump;
    let mut listener = Listener::new(&listener_settings);
    listener.path(line.delay);
    let device = Device {
        rate: RATE,
        channels: CHANNELS,
        cycle: scene.cycle,
        drift: 0,
        start: line.offset,
        lead: 4_000_000,
        hidden: 0,
    };
    // The cycles that are asked for by the end leave up to the lead later.
    let mut output = Output::new(device, 50_500 + scene.cycle);
    let until = line.offset + 1_000_000_000;
    run(&mut line, &mut listener, &mut output, until, before);
    assert_eq!(output.unrecorded(), 0);
    let recorded = output.recorded();
    Outcome {
        first: recorded.iter().step_by(2).copied().collect(),
        second: recorded.iter().skip(1).step_by(2).copied().collect(),
        totals: listener.totals(),
    }
}

/// The device's count of the first frame that is not silent.
fn first_sound(outcome: &Outcome) -> u64 {
    let place = outcome.first.iter().position(|sample| *sample != 0.0);
    place.expect("the device played something") as u64
}

/// The number of frames that the pump skips when it begins to play: the
/// frames from the first one of the stream, which arrived before the
/// sender's clock was known, up to the first one that the filter needs for
/// the first frame it plays.
fn skipped_at_the_start(outcome: &Outcome) -> u64 {
    let before = Filter::for_rate(RATE).before() as u64;
    first_sound(outcome) - LEVEL_FRAMES - before
}

/// A wrong position, a frame offset, samples from the wrong index or from
/// the wrong channel, and a dependence on how the device cuts its cycles
/// would each put another frame, or none, where this one is due.
#[test]
fn each_frame_leaves_the_device_when_it_is_due_whatever_the_cycle() {
    for cycle in [64, 250, 441] {
        let outcome = whole_frames(&Scene { cycle, ..scene() }, |_, _| {});
        let start = first_sound(&outcome);
        // The sender's clock is known after the second window of packets,
        // 55 ms in, and then the first cycle that is asked for plays.
        assert!(start < 4_500, "cycle {cycle}: first sound at frame {start}");
        assert!(outcome.first.len() > 45_000);
        for (count, (first, second)) in (0u64..).zip(outcome.first.iter().zip(&outcome.second)) {
            if count < start {
                assert!(*first == 0.0 && *second == 0.0);
            } else {
                assert_eq!(
                    index_of(*first),
                    Some(count - LEVEL_FRAMES),
                    "cycle {cycle}, device frame {count}"
                );
                assert_eq!(*second, -*first);
            }
        }
        // Every frame was there when it was needed.
        assert_eq!((outcome.totals.concealed, outcome.totals.behind), (0, 0));
        assert_eq!(outcome.totals.jumps, 1);
        assert_eq!(outcome.totals.skipped, skipped_at_the_start(&outcome));
    }
}

/// A concealment that covers frames that are there, or misses frames that
/// are not, or a store that gives a missing frame the samples of another,
/// would show as silence or as a frame in the wrong place.
#[test]
fn lost_packets_are_concealed_exactly_where_their_frames_are() {
    let lost = [40, 41, 77];
    let with_losses = Scene {
        lost: lost.to_vec(),
        ..scene()
    };
    let outcome = whole_frames(&with_losses, |_, _| {});
    let start = first_sound(&outcome);
    for (count, sample) in (0u64..)
        .zip(&outcome.first)
        .skip(usize::try_from(start).unwrap_or(0))
    {
        let index = count - LEVEL_FRAMES;
        if lost.contains(&(index / u64::from(PACKET))) {
            assert!(*sample == 0.0, "frame {index} of a lost packet was played");
        } else {
            assert_eq!(index_of(*sample), Some(index));
        }
    }
    assert_eq!(outcome.totals.concealed, 3 * u64::from(PACKET));
    assert_eq!(outcome.totals.behind, 0);
}

/// With the fades of a real stream, the frames around a gap are changed for
/// the length of the gap and of the fade in after it, and no others.
#[test]
fn a_gap_and_the_fade_in_after_it_are_all_that_a_lost_packet_changes() {
    let concealment = Parameters::for_rate(RATE);
    let with_fades = Scene {
        concealment,
        lost: vec![40],
        ..scene()
    };
    let outcome = whole_frames(&with_fades, |_, _| {});
    let gap = 40 * u64::from(PACKET)..41 * u64::from(PACKET);
    let changed = gap.start..gap.end + concealment.fade_in as u64;
    let mut continued = 0;
    for (count, sample) in (0u64..).zip(&outcome.first).skip(6_500) {
        let index = count - LEVEL_FRAMES;
        if !changed.contains(&index) {
            assert_eq!(index_of(*sample), Some(index));
        } else if gap.contains(&index) && *sample != 0.0 && index_of(*sample) != Some(index) {
            continued += 1;
        }
    }
    // The gap is filled with a continuation of the sound, not with the
    // frames that were lost and not with silence from its first frame on.
    assert!(
        continued > 200,
        "{continued} frames of the gap were continued"
    );
    assert_eq!(outcome.totals.concealed, u64::from(PACKET));
}

/// The frames of an outcome that are not silent, as the device's count and
/// the index of the stream's frame.
fn sounding(outcome: &Outcome) -> Vec<(u64, u64)> {
    (0u64..)
        .zip(&outcome.first)
        .filter(|(_, sample)| **sample != 0.0)
        .map(|(count, sample)| {
            let index = index_of(*sample).expect("a frame of the stream, unchanged");
            (count, index)
        })
        .collect()
}

/// Ten milliseconds, which is 500 frames: more than the receiver plays away
/// by changing its pace.
const STEP: i64 = 10_000_000;
const STEP_FRAMES: u64 = 500;

/// When the level drops, the frames that are due are further on in the
/// stream. A pump that kept its frames across the jump, or did not skip,
/// would play frames again or out of order.
#[test]
fn a_jump_ahead_skips_frames_and_plays_none_twice() {
    let short_cycles = Scene {
        cycle: 100,
        ..scene()
    };
    let outcome = whole_frames(&short_cycles, |number, sender| {
        if number == 60 {
            sender.level(LEVEL - STEP, 0);
        }
    });
    let frames = sounding(&outcome);
    assert!(frames.windows(2).all(|pair| pair[0].1 < pair[1].1));
    // From its first sound on the device is never silent, and each frame is
    // the one due at the level before or after the change, in that order.
    let start = first_sound(&outcome);
    assert_eq!(frames.len() as u64, outcome.first.len() as u64 - start);
    let after = frames
        .iter()
        .position(|(count, index)| *index == count - (LEVEL_FRAMES - STEP_FRAMES))
        .expect("the new level was taken up");
    assert!(after > 10_000 && after < frames.len() - 10_000);
    for (place, (count, index)) in frames.iter().enumerate() {
        let level = if place < after {
            LEVEL_FRAMES
        } else {
            LEVEL_FRAMES - STEP_FRAMES
        };
        assert_eq!(*index, count - level);
    }
    // The frames skipped are the 500 of the jump less those that the pump
    // had taken ahead of its position for the filter: one less than the
    // filter has taps.
    let taps = Filter::for_rate(RATE).taps() as u64;
    assert_eq!(
        outcome.totals.skipped,
        skipped_at_the_start(&outcome) + STEP_FRAMES + 1 - taps
    );
    assert_eq!(outcome.totals.jumps, 2);
}

/// When the level rises, the frames that are due are ones that the receiver
/// has played. A pump that went back into its store would play them again.
#[test]
fn a_jump_back_waits_in_silence_and_plays_none_twice() {
    let short_cycles = Scene {
        cycle: 100,
        ..scene()
    };
    let outcome = whole_frames(&short_cycles, |number, sender| {
        if number == 60 {
            sender.level(LEVEL + STEP, 0);
        }
    });
    let frames = sounding(&outcome);
    assert!(frames.windows(2).all(|pair| pair[0].1 < pair[1].1));
    let after = frames
        .iter()
        .position(|(count, index)| *index == count - (LEVEL_FRAMES + STEP_FRAMES))
        .expect("the new level was taken up");
    assert!(after > 10_000 && after < frames.len() - 10_000);
    for (place, (count, index)) in frames.iter().enumerate() {
        let level = if place < after {
            LEVEL_FRAMES
        } else {
            LEVEL_FRAMES + STEP_FRAMES
        };
        assert_eq!(*index, count - level);
    }
    // The device is silent while the schedule comes up to the playhead: for
    // the 500 frames of the jump and for the frames that the pump had taken
    // ahead of its position, which are not given again.
    let ahead = Filter::for_rate(RATE).ahead() as u64;
    let taps = Filter::for_rate(RATE).taps() as u64;
    let silent = frames[after].0 - frames[after - 1].0 - 1;
    assert_eq!(silent, STEP_FRAMES + ahead);
    assert_eq!(frames[after].1, frames[after - 1].1 + 1 + ahead);
    assert_eq!(outcome.totals.behind, STEP_FRAMES + taps - 1);
    assert_eq!(outcome.totals.skipped, skipped_at_the_start(&outcome));
    assert_eq!(outcome.totals.jumps, 2);
}

/// A jump back by less than the filter reaches: the frames that are due
/// again are among those the pump has kept for the filter. A pump that went
/// on with its kept frames would play them a second time.
#[test]
fn a_short_jump_back_plays_no_kept_frame_again() {
    let hop = 5;
    let eager = Scene {
        cycle: 100,
        jump: 2,
        ..scene()
    };
    let outcome = whole_frames(&eager, |number, sender| {
        if number == 60 {
            sender.level(LEVEL + 20_000 * 5, 0);
        }
    });
    let frames = sounding(&outcome);
    assert!(frames.windows(2).all(|pair| pair[0].1 < pair[1].1));
    let after = frames
        .iter()
        .position(|(count, index)| *index == count - (LEVEL_FRAMES + hop))
        .expect("the new level was taken up");
    assert!(after > 10_000 && after < frames.len() - 10_000);
    let ahead = Filter::for_rate(RATE).ahead() as u64;
    assert_eq!(frames[after].0 - frames[after - 1].0 - 1, hop + ahead);
    assert_eq!(frames[after].1, frames[after - 1].1 + 1 + ahead);
    assert_eq!(outcome.totals.jumps, 2);
}

/// A copy of a packet that arrives when its frames are long played has no
/// room, but its frames have the places of frames a store's length further
/// on, which are held and not yet played. A store that wrote it anyway
/// would play old frames in their place.
#[test]
fn a_copy_of_an_old_packet_does_not_overwrite_held_frames() {
    // With packet 90, whose arrival is 456.5 ms in, arrives a copy of packet
    // 70, the frames 17,500 to 17,749. The store has 4,096 places, so these
    // have the places of the frames 21,596 to 21,845, which arrived with
    // the packets 86 and 87 and are due from 461.9 ms on.
    let with_copy = Scene {
        repeated: vec![(90, 70)],
        ..scene()
    };
    let outcome = whole_frames(&with_copy, |_, _| {});
    let start = first_sound(&outcome);
    let from = usize::try_from(start).unwrap_or(0);
    for (count, sample) in (0u64..).zip(&outcome.first).skip(from) {
        assert_eq!(index_of(*sample), Some(count - LEVEL_FRAMES));
    }
    assert_eq!(outcome.totals.concealed, 0);
}

/// Two tones: 1 kHz on the first channel and 7 kHz, at another level and
/// phase, on the second.
fn tone(channel: usize) -> (f64, f64, f64) {
    if channel == 0 {
        (0.5, 1_000.0, 0.0)
    } else {
        (0.25, 7_000.0, 1.0)
    }
}

/// The tones at a position of a stream of 48,000 frames a second.
fn tones_at(position: f64, channel: usize) -> f64 {
    let (level, hertz, phase) = tone(channel);
    level * (TAU * hertz * position / 48_000.0 + phase).sin()
}

fn tones(index: u64, channel: usize) -> f32 {
    // An index below 2^53 is exact as a float; the sample is rounded to f32.
    #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
    let sample = tones_at(index as f64, channel) as f32;
    sample
}

/// A scene with clocks and a device that drift: the receiver's clock gains
/// 30 parts per million on the sender's, and the device 200 on the
/// receiver's.
fn drifting(hidden: i64, block: usize, seconds: i64) -> (Line, Output) {
    let mut line = Line::new(48_000, 240, LEVEL, tones);
    line.skew = 30_000;
    line.offset += 123_457;
    let mut listener_settings = settings(48_000, Parameters::for_rate(48_000));
    listener_settings.block = block;
    let mut listener = Listener::new(&listener_settings);
    // The delay of the path on the receiver's clock.
    listener.path(line.delay + line.delay * line.skew / 1_000_000_000);
    let device = Device {
        rate: 48_000,
        channels: CHANNELS,
        cycle: 256,
        drift: 200_000,
        start: line.offset + 777,
        lead: 4_000_000,
        hidden,
    };
    let frames = usize::try_from(seconds).unwrap_or(0) * 48_100 + 1_000;
    let mut output = Output::new(device, frames);
    let until = line.offset + seconds * 1_000_000_000;
    run(&mut line, &mut listener, &mut output, until, |_, _| {});
    assert_eq!(output.unrecorded(), 0);
    (line, output)
}

/// The largest difference, over the frames that left the device after
/// `from` seconds, between what the device played and the tones that were
/// due `late` nanoseconds before each frame left.
fn largest_error(line: &Line, output: &Output, from: i64, late: i64) -> f64 {
    let device = output.device();
    let mut largest = 0.0f64;
    for (count, frame) in (0u64..).zip(output.recorded().as_chunks::<CHANNELS>().0) {
        let left = device.played(count);
        if left < line.offset + from * 1_000_000_000 {
            continue;
        }
        // The sender's clock at that time, and the position that is due.
        #[allow(clippy::cast_precision_loss)]
        let sender = (left - late - line.offset) as f64 / (1.0 + line.skew as f64 * 1e-9);
        #[allow(clippy::cast_precision_loss)]
        let position = (sender - LEVEL as f64) * 48_000.0 * 1e-9;
        for (channel, sample) in frame.iter().enumerate() {
            largest = largest.max((f64::from(*sample) - tones_at(position, channel)).abs());
        }
    }
    largest
}

/// The resampler's error for a tone is 110 dB below it, which is 1.6e-6 of
/// the louder tone here. A timing error of `d` seconds shows as `2 pi f d`
/// of a tone of `f` hertz: the bound allows 9 nanoseconds at 7 kHz. A frame
/// offset is two thousand times that, and a cycle length that is always
/// rounded down to a whole nanosecond is ten times that.
const TONE_BOUND: f64 = 1e-4;

#[test]
fn a_tone_comes_out_on_schedule_from_a_device_that_drifts() {
    let (line, output) = drifting(0, 256, 6);
    let error = largest_error(&line, &output, 4, 0);
    assert!(error < TONE_BOUND, "largest error {error}");
}

/// The receiver schedules by the times that its device reports. What the
/// device does not report, the sound is late by.
#[test]
fn a_delay_that_the_device_hides_makes_the_sound_late_by_it() {
    let hidden = 250_000;
    let (line, output) = drifting(hidden, 256, 6);
    let late = largest_error(&line, &output, 4, hidden);
    assert!(late < TONE_BOUND, "largest error {late}");
    // Held against the true times, the tones are off by a quarter of a
    // millisecond, which is more than a cycle of 7 kHz.
    let on_time = largest_error(&line, &output, 4, 0);
    assert!(on_time > 0.2, "largest error {on_time}");
}

/// How many output frames the pump computes in one go changes nothing: a
/// frame is a function of its position and of the stream.
#[test]
fn the_size_of_the_pump_s_blocks_does_not_change_the_output() {
    let (_, small) = drifting(0, 32, 2);
    let (_, large) = drifting(0, 100_000, 2);
    assert!(small.recorded().iter().any(|sample| *sample != 0.0));
    let same = small.recorded() == large.recorded();
    assert!(same, "the outputs differ");
}

fn tone_header(index: u64, rate: u32) -> unisono_core::packet::Audio {
    let capture = i64::try_from(index).unwrap_or(0) * 20_833;
    unisono_core::packet::Audio {
        stream: 1,
        timeline: 1,
        index,
        frames: 240,
        rate,
        channels: 2,
        format: unisono_core::packet::Format::Signed24,
        flags: 0,
        protection: 0,
        window: 2400,
        span: 2000,
        capture,
        drift: 0,
        level: LEVEL,
        level_slope: 0,
        stamped_index: 0,
        stamped_departure: 0,
        clock: 1,
    }
}

/// Cycles with nothing to play (`plan.frames == 0`) after a tone fade the tone
/// out through the concealment instead of cutting it, reach exact silence,
/// and when playing starts again, nothing of the tone before comes back.
#[test]
fn idle_cycles_fade_out_without_click_and_resume_cleanly() {
    use unisono_core::packet::Format;
    use unisono_core::player::{Plan, Regulation};
    use unisono_core::receiver::{Receiver, Settings as ReceiverSettings};
    use unisono_dsp::format::to_signed24;
    use unisono_dsp::{Position, Step};
    use unisono_runtime::pump::Pump;
    use unisono_runtime::store::Store;

    let rate = 48_000u32;
    let params = Parameters::for_rate(rate);
    let mut receiver = Receiver::<64, 64, 8>::new(ReceiverSettings {
        stream: 1,
        identity: 1,
        silence: 1_000_000_000,
        limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: 240,
        },
    });
    let mut store = Store::for_stretch(64, CHANNELS);
    let mut pump = Pump::new(Filter::for_rate(rate), CHANNELS, params, 256);

    // Feed 3,600 frames of 1 kHz / 7 kHz tones so the pump is well past fade-in.
    let mut payload = vec![0u8; 240 * CHANNELS * 3];
    let mut samples = vec![0.0f32; 240 * CHANNELS];
    for p in 0..15u64 {
        let index = p * 240;
        for f in 0..240usize {
            samples[f * 2] = tones(index + f as u64, 0);
            samples[f * 2 + 1] = tones(index + f as u64, 1);
        }
        to_signed24(&samples, &mut payload);
        let header = tone_header(index, rate);
        let heard = receiver.packet(&header, header.capture);
        assert!(!heard.ignored);
        store.write_packet(index, Format::Signed24, &payload, |i| receiver.covers(i));
    }

    // Play 8 active cycles (2,048 frames), ending well into the 1 kHz wave.
    let mut last_active = vec![0.0f32; 256 * CHANNELS];
    for c in 0..8u64 {
        let plan = Plan {
            frames: 256,
            start: Position::at_frame(c * 256),
            step: Step::UNITY,
            jumped: c == 0,
        };
        pump.play(&mut receiver, &store, &plan, &mut last_active);
    }
    let last_ch0 = last_active[255 * CHANNELS];
    assert!(
        last_ch0.abs() > 0.1,
        "expected active tone at stop boundary, got {last_ch0}"
    );

    // Feed 10 idle cycles (~53 ms, longer than fade_out + filter taps).
    let idle = Plan {
        frames: 0,
        start: Position::at_frame(0),
        step: Step::UNITY,
        jumped: false,
    };
    let mut idle_out = Vec::new();
    let mut buf = vec![0.0f32; 256 * CHANNELS];
    for _ in 0..10 {
        let done = pump.play(&mut receiver, &store, &idle, &mut buf);
        assert_eq!((done.played, done.silent), (0, 256));
        idle_out.extend_from_slice(&buf);
    }

    // Transition across the stop boundary must be continuous (no hard cut
    // to 0.0 and no phase-reversal jump). For a 1 kHz tone of amplitude 0.5
    // at 48 kHz, max natural sample-to-sample step is 0.5 * 2*pi/48 ≈ 0.065.
    let boundary_step = (idle_out[0] - last_ch0).abs();
    assert!(
        boundary_step < 0.08,
        "click across stop boundary: last={last_ch0}, first_idle={}, step={boundary_step}",
        idle_out[0]
    );
    assert!(
        idle_out[..256 * CHANNELS].iter().any(|s| *s != 0.0),
        "expected smooth fade-out in first idle cycle"
    );
    assert!(
        idle_out[7 * 256 * CHANNELS..].iter().all(|s| *s == 0.0),
        "expected exact silence after fade-out completes"
    );

    // Playing starts again on frames of silence; the output must be silent,
    // with nothing of the tone played before the cycles without frames.
    let zero_payload = vec![0u8; 240 * CHANNELS * 3];
    for p in 15..18u64 {
        let index = p * 240;
        let header = tone_header(index, rate);
        receiver.packet(&header, header.capture);
        store.write_packet(index, Format::Signed24, &zero_payload, |i| {
            receiver.covers(i)
        });
    }
    let resume = Plan {
        frames: 256,
        start: Position::at_frame(15 * 240 + 64),
        step: Step::UNITY,
        jumped: true,
    };
    pump.play(&mut receiver, &store, &resume, &mut buf);
    let loudest = buf.iter().map(|s| s.abs()).fold(0.0f32, f32::max);
    assert!(
        loudest < 1e-6,
        "the tone came back after the silence: {loudest}"
    );
}

/// Exchanging reports and echoes through `ReceiverPlayback` measures the path
/// delay without manual configuration, and the device line keeps a drifting
/// device locked on schedule.
#[test]
fn report_and_echo_exchange_measures_path_delay_on_receiver_playback() {
    let mut line = Line::new(48_000, 240, LEVEL, tones);
    line.delay = 2_000_000;
    line.skew = 30_000;
    let mut listener = Listener::new(&settings(48_000, Parameters::for_rate(48_000)));
    // Do NOT call `listener.path(...)`: let reports and echoes measure it.
    assert_eq!(listener.receiver().delay(), 0);
    let device = Device {
        rate: 48_000,
        channels: CHANNELS,
        cycle: 256,
        drift: 200_000,
        start: line.offset + 777,
        lead: 4_000_000,
        hidden: 0,
    };
    let mut output = Output::new(device, 8 * 48_100 + 1_000);
    let until = line.offset + 8_000_000_000;
    // Send a report every 10th packet (every 50 ms = 20 Hz) and echo it back
    // after the symmetric one-way path delay.
    let mut next_report_packet = 10u64;
    loop {
        if line.under_way.is_none() {
            let sent = line.send();
            line.under_way = Some(sent);
        }
        let next_packet = line
            .under_way
            .as_ref()
            .map_or(i64::MAX, |sent| sent.arrival);
        let next_cycle = output.due();
        if next_packet > until && next_cycle > until {
            break;
        }
        if next_packet <= next_cycle {
            let sent = line.under_way.take().expect("packet under way");
            listener.packet(&sent.header, &sent.payload, sent.arrival);
            if sent.number >= next_report_packet {
                next_report_packet += 10;
                if let Some(report) = listener.report() {
                    let sender_now = line.captured((sent.number + 1) * u64::from(line.packet))
                        + line.send
                        + line.delay;
                    let departure = line.receiver_clock(sender_now);
                    listener.reported(report.sequence, departure);
                    let arrival_at_sender = sender_now + line.delay;
                    if let Some(echo) = line.sender.answer(&report, arrival_at_sender) {
                        listener.echo(&echo);
                    }
                }
            }
        } else {
            output.cycle(&mut listener);
        }
    }
    let measured = listener.receiver().delay();
    assert!(
        (measured - line.delay).abs() <= 5,
        "measured path {measured} vs expected {}",
        line.delay
    );
    // `measure_path` yields the one-way delay in sender-clock nanoseconds,
    // which differs from receiver-clock nanoseconds by `delay * skew` (60 ns).
    let skew_residual = line.delay * line.skew / 1_000_000_000;
    let error = largest_error(&line, &output, 6, skew_residual);
    assert!(error < TONE_BOUND, "largest error {error}");
    let raw_error = largest_error(&line, &output, 6, 0);
    assert!(raw_error < 3e-3, "largest raw error {raw_error}");
}
