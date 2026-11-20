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

mod common;

use std::net::SocketAddr;
use std::time::Duration;

use common::{CHANNELS, settings};
use unisono_core::packet::Format;
use unisono_core::sender::Settings as StreamSettings;
use unisono_dsp::Parameters;
use unisono_runtime::clock;
use unisono_runtime::pump::ReceiverPlayback;
use unisono_runtime::receive::{self, Intake, ReceiverAudio, ReceiverNetwork, Sizes};
use unisono_runtime::send::{self, SenderNetwork, Settings};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Input, Output};

/// The latency that the receiver holds: 30 ms.
const LEVEL: i64 = 30_000_000;
const RATE: u32 = 48_000;

/// The ramp's sample of the frame counted as `position`.
fn ramp(position: u64) -> f32 {
    // A count below 2^23 is exact as a float.
    #[allow(clippy::cast_precision_loss)]
    let value = (position + 1) as f32 / 8_388_608.0;
    value
}

#[test]
fn frames_play_a_level_after_they_were_captured() {
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
            timeline: send::first_timeline(),
            receivers: vec![address],
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
    let playback: ReceiverPlayback<64, 64, 8, 64> =
        ReceiverPlayback::new(&settings(RATE, Parameters::for_rate(RATE)));
    let mut audio = ReceiverAudio::new(
        playback,
        audio_end,
        Intake {
            items: 8,
            report_period: 50_000_000,
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
    let seconds = 8;
    let frames = usize::try_from(seconds).unwrap_or(0) * 48_000 + 1_000;
    let mut output = Output::new(device, frames);

    let end = start + seconds * 1_000_000_000;
    loop {
        let now = clock::raw();
        if now > end {
            break;
        }
        input.run(now, &mut capture_end);
        sender.turn(0).expect("the sender");
        network.turn(0).expect("the receiver's network end");
        output.run(now, &mut audio);
        std::thread::sleep(Duration::from_micros(500));
    }

    assert_eq!(capture_end.dropped(), 0);
    let sent = sender.counts();
    assert_eq!(
        (sent.filled, sent.restarts, sent.unsent),
        (0, 0, 0),
        "{sent:?}"
    );
    assert!(sent.answers > 10, "{sent:?}");
    let received = network.counts();
    assert_eq!(received.dropped, 0, "{received:?}");
    assert!(
        received.packets + 2 >= sent.packets,
        "{received:?} against {sent:?}"
    );

    let mut errors = errors(input.device(), &output, end - 3_000_000_000);
    assert!(errors.len() > 140_000, "{} frames", errors.len());
    errors.sort_by(f64::total_cmp);
    let (low, high) = (errors[errors.len() / 50], errors[errors.len() * 49 / 50]);
    assert!(low > -20e-6 && high < 20e-6, "from {low} to {high}");
}

/// How far from the level the latency is of each frame that `output` played
/// from `from` on: the time it left the playback device, less the time the
/// device `capture` took it, less the level, in seconds.
fn errors(capture: &Device, output: &Output, from: i64) -> Vec<f64> {
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
        errors.push((left as f64 - taken - LEVEL as f64) * 1e-9);
    }
    errors
}
