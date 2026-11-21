// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A sender and a receiver, each on its two threads' ends, with real sockets
//! on the loopback interface and the host's raw clock: a software capture
//! device hands its frames to the sender, and a software playback device
//! plays what the receiver gives it. The two devices run at rates of their
//! own, as devices do.
//!
//! The capture device captures a ramp: the sample of the frame it counts as
//! `i` is `(i + 1) / 2^23`. A sample that comes out of the playback device
//! therefore says which captured frame it is, to a small fraction of one,
//! and with the time at which the capture device took that frame and the
//! time at which the playback device plays it, how far from the level the
//! latency is.

//!
//! The level is held in one test; in the other the sender chooses it from
//! the needs that the receiver reports, and moves it there.

mod common;

use std::net::SocketAddr;
use std::time::Duration;

use common::{CHANNELS, settings};
use unisono_core::packet::Format;
use unisono_core::sender::Settings as StreamSettings;
use unisono_dsp::Parameters;
use unisono_runtime::clock;
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::pump::{ReceiverPlayback, Revisions, Totals};
use unisono_runtime::receive::{
    self, Intake, NetworkCounts, ReceiverAudio, ReceiverNetwork, Reporting, Sizes,
};
use unisono_runtime::send::{self, SenderCounts, SenderNetwork, Settings};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Input, Output};

/// The latency that the receiver holds at the start: 30 ms.
const LEVEL: i64 = 30_000_000;
const RATE: u32 = 48_000;

/// The ramp's sample of the frame counted as `position`.
fn ramp(position: u64) -> f32 {
    // A count below 2^23 is exact as a float.
    #[allow(clippy::cast_precision_loss)]
    let value = (position + 1) as f32 / 8_388_608.0;
    value
}

/// What a run of a sender and a receiver did.
struct Run {
    sent: SenderCounts,
    /// What the receiver played.
    played: Totals,
    /// How the receiver's schedule was revised from cycle to cycle.
    revisions: Revisions,
    /// The level at the end, in nanoseconds.
    level: i64,
    /// The lowest and the highest level on the way, in nanoseconds.
    range: (i64, i64),
    /// How far from the level that the sender held for it the latency was,
    /// in seconds, of each frame played in the last three seconds.
    errors: Vec<f64>,
}

/// Runs a sender whose level is chosen as `choice` says, and a receiver
/// whose pace may differ from the stream's by `limit` parts per billion,
/// for `seconds` seconds, and checks that nothing was lost on the way.
fn run(choice: Option<Choice>, limit: u32, seconds: i64) -> Run {
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("an address");
    let receiving = Socket::bind(loopback).expect("a socket");
    let address = receiving.address().expect("its address");
    let start = clock::raw();

    // The sender: a capture device 50 parts per million fast.
    let capture = Device {
        rate: RATE,
        channels: CHANNELS,
        cycle: 256,
        drift: 50_000,
        start,
        lead: 1_000_000,
        hidden: 0,
    };
    let mut input = Input::new(capture, |position, _, frame: &mut [f32]| {
        frame[0] = ramp(position);
        frame[1] = -ramp(position);
    });
    let (mut capture_end, sender_end) = send::link(16, 256, CHANNELS);
    let mut sender = SenderNetwork::new(
        Socket::bind(loopback).expect("a socket"),
        sender_end,
        Settings {
            stream: StreamSettings {
                stream: 1,
                rate: RATE,
                channels: 2,
                format: Format::Signed24,
                span: 2_000,
                window: 2_400,
                clock: send::clock_identity(),
            },
            packet: 240,
            level: LEVEL,
            choice,
            timeline: send::first_timeline(),
            receivers: vec![address],
            kept: 0,
        },
    );

    // The receiver: a playback device 80 parts per million slow.
    let sizes = Sizes {
        buffers: 32,
        datagram: 2_048,
        messages: 64,
    };
    let (network_end, audio_end) = receive::link(sizes);
    let mut network = ReceiverNetwork::new(receiving, network_end, 1, sizes);
    let mut listening = settings(RATE, Parameters::for_rate(RATE));
    listening.regulation.limit = limit;
    let playback: ReceiverPlayback<64, 64, 8, 64> = ReceiverPlayback::new(&listening);
    let mut audio = ReceiverAudio::new(
        playback,
        audio_end,
        Intake {
            items: 8,
            reports: Some(Reporting::USUAL),
        },
    );
    let device = Device {
        rate: RATE,
        channels: CHANNELS,
        cycle: 256,
        drift: -80_000,
        start: start + 3_000_000,
        lead: 4_000_000,
        hidden: 0,
    };
    let frames = usize::try_from(seconds).unwrap_or(0) * 48_000 + 1_000;
    let mut output = Output::new(device, frames);

    let end = start + seconds * 1_000_000_000;
    // The level that the sender holds for the frame with each index, as far
    // as the loop sees it: between two turns it moves along a line.
    let mut levels: Vec<(u64, i64)> = Vec::new();
    loop {
        let now = clock::raw();
        if now > end {
            break;
        }
        input.run(now, &mut capture_end);
        sender.turn(0).expect("the sender");
        levels.push((sender.sender().next(), sender.sender().current_level()));
        network.turn(0).expect("the receiver's network end");
        output.run(now, &mut audio);
        std::thread::sleep(Duration::from_micros(500));
    }

    let sent = sender.counts();
    nothing_lost(capture_end.dropped(), sent, network.counts());
    let lowest = levels.iter().map(|(_, level)| *level).min().unwrap_or(0);
    let highest = levels.iter().map(|(_, level)| *level).max().unwrap_or(0);
    Run {
        sent,
        played: audio.playback().totals(),
        revisions: audio.playback().revisions(),
        level: sender.sender().current_level(),
        range: (lowest, highest),
        errors: errors(input.device(), &output, end - 3_000_000_000, &levels),
    }
}

/// Checks that the capture thread dropped no cycle, that the sender sent
/// every packet and answered reports, and that the receiver's network thread
/// handed every packet over.
fn nothing_lost(dropped: u64, sent: SenderCounts, received: NetworkCounts) {
    assert_eq!(dropped, 0);
    assert_eq!(
        (sent.filled, sent.restarts, sent.unsent),
        (0, 0, 0),
        "{sent:?}"
    );
    assert!(sent.answers > 10, "{sent:?}");
    assert_eq!(received.dropped, 0, "{received:?}");
    assert!(
        received.packets + 2 >= sent.packets,
        "{received:?} against {sent:?}"
    );
}

/// The 2nd and the 98th percentile of `errors`.
fn spread(errors: &mut [f64]) -> (f64, f64) {
    errors.sort_by(f64::total_cmp);
    (errors[errors.len() / 50], errors[errors.len() * 49 / 50])
}

#[test]
fn frames_play_a_level_after_they_were_captured() {
    let mut run = run(None, 1_000_000, 8);
    assert_eq!(run.level, LEVEL);
    assert!(run.errors.len() > 140_000, "{} frames", run.errors.len());
    let (low, high) = spread(&mut run.errors);
    assert!(low > -20e-6 && high < 20e-6, "from {low} to {high}");
    // The schedule is revised at the start of nearly every cycle, by small
    // fractions of a frame, and the products of successive revisions are
    // within what their squares allow.
    let revisions = run.revisions;
    println!("revisions {revisions:?}");
    assert!(
        revisions.count * 10 > run.played.cycles * 9,
        "{revisions:?} in {:?}",
        run.played
    );
    assert!(
        revisions.squares > 0.0 && revisions.products.abs() <= revisions.squares,
        "{revisions:?}"
    );
}

#[test]
fn the_level_moves_to_what_the_receiver_needs_and_frames_follow_it() {
    // Stretches of 50 ms. A gap is priced low, so that a few seconds of
    // evidence are enough to bring the level down to the needs: a gap costs
    // as much as a millisecond of level held for six seconds. The level
    // moves by 2 ms a second, which the receiver's pace can follow: the pace
    // is held within three in a thousand whatever limit is set.
    let choice = Choice {
        weights: Weights {
            latency: 1_000.0,
            target: 0,
            off_target: 0.0,
            gap: 6.0,
            missed: 600.0,
            moving: 1.0,
        },
        history: 2_400,
        slope: 2_000_000,
    };
    let run = run(Some(choice), 20_000_000, 10);
    // The first frame of a packet waits 5 ms for the packet to fill, up to a
    // cycle of the capture device and its lead, 6.3 ms, and up to a cycle of
    // the playback device and its lead, 9.3 ms: a level of about 20 ms is
    // what the frames need, and the level comes down to that from 30 ms.
    assert!(run.sent.moves >= 1, "{:?}", run.sent);
    assert!(
        run.level > 16_000_000 && run.level < 26_000_000,
        "level {}, {:?}",
        run.level,
        run.sent
    );
    assert!(run.range.1 <= LEVEL, "the level rose to {}", run.range.1);
    // Where the level settles, a frame now and then needs a little more
    // than any before it: nearly all frames are played from the stream.
    assert!(
        run.played.concealed * 100 < run.played.played && run.played.behind == 0,
        "{:?}",
        run.played
    );
    // Each frame plays at the level that the sender held for it, while the
    // level moves and after: a change of the level's slope holds from the
    // packet that brings it, not from when that packet arrives.
    assert!(run.errors.len() > 140_000, "{} frames", run.errors.len());
    // A sample that the concealment made says nothing of when its frame
    // was captured; a frame from the stream is within milliseconds.
    let mut stream: Vec<f64> = run
        .errors
        .iter()
        .copied()
        .filter(|error| error.abs() < 5e-3)
        .collect();
    assert!(
        stream.len() * 100 >= run.errors.len() * 90,
        "{} of {} frames from the stream",
        stream.len(),
        run.errors.len()
    );
    let (low, high) = spread(&mut stream);
    assert!(low > -50e-6 && high < 50e-6, "from {low} to {high}");
}

/// The level that the sender held for the frame at `position`, by the
/// `levels` seen at the turns of the loop, in nanoseconds.
fn level_at(levels: &[(u64, i64)], position: f64) -> f64 {
    // An index and a level in nanoseconds are far below 2^52.
    #[allow(clippy::cast_precision_loss)]
    let point = |(index, level): (u64, i64)| (index as f64, level as f64);
    let after = levels.partition_point(|&seen| point(seen).0 <= position);
    match (
        after.checked_sub(1).and_then(|at| levels.get(at)),
        levels.get(after),
    ) {
        (Some(&before), Some(&next)) => {
            let ((from, low), (to, high)) = (point(before), point(next));
            if to > from {
                low + (high - low) * (position - from) / (to - from)
            } else {
                low
            }
        }
        (Some(&seen), None) | (None, Some(&seen)) => point(seen).1,
        (None, None) => 0.0,
    }
}

/// How far from its level the latency is of each frame that `output` played
/// from `from` on: the time it left the playback device, less the time the
/// device `capture` took it, less the level that the sender held for it, in
/// seconds.
fn errors(capture: &Device, output: &Output, from: i64, levels: &[(u64, i64)]) -> Vec<f64> {
    let mut errors = Vec::new();
    for (count, frame) in (0u64..).zip(output.recorded().as_chunks::<CHANNELS>().0) {
        let left = output.device().played(count);
        if left < from || frame[0] == 0.0 {
            continue;
        }
        let position = f64::from(frame[0]) * 8_388_608.0 - 1.0;
        if position < 0.0 {
            continue;
        }
        // The capture time between the two frames around the position. A
        // position below 2^23 is exact as an integer.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let whole = position.floor() as u64;
        let (before, after) = (capture.captured(whole), capture.captured(whole + 1));
        #[allow(clippy::cast_precision_loss)]
        let taken = before as f64 + (after - before) as f64 * position.fract();
        #[allow(clippy::cast_precision_loss)]
        errors.push((left as f64 - taken - level_at(levels, position)) * 1e-9);
    }
    errors
}
