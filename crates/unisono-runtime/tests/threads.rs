// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A receiver's two ends with real sockets, on the loopback interface and
//! the host's raw clock: a sender sends a stream and answers reports, the
//! network end of the receiver takes datagrams in, and a software device
//! plays what the audio end gives it.
//!
//! The stream is a ramp: the sample of frame `i` is `(i + 1) / 2^23`, so a
//! sample that comes out of the device says which position of the stream it
//! is, to a small fraction of a frame, and with the time at which the device
//! plays it, how late it is. Here every clock is the same clock, so a frame
//! captured at `t` is due at `t` plus the level.

mod common;

use std::net::SocketAddr;
use std::time::Duration;

use common::{CHANNELS, settings};
use unisono_core::packet::{self, Format, KIND_REPORT, parse_report, write_audio, write_echo};
use unisono_core::sender::{Sender, Settings as SenderSettings};
use unisono_dsp::Parameters;
use unisono_dsp::format::to_signed24;
use unisono_runtime::clock;
use unisono_runtime::proxy::{Impairment, Proxy};
use unisono_runtime::pump::ReceiverPlayback;
use unisono_runtime::receive::{
    Intake, NetworkCounts, ReceiverAudio, ReceiverNetwork, Sizes, link,
};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Output};

/// The latency that the receiver holds: 30 ms.
const LEVEL: i64 = 30_000_000;
const RATE: u32 = 48_000;
const PACKET: u16 = 240;

/// The ramp's sample of frame `index`.
fn ramp(index: u64) -> f32 {
    // An index below 2^23 is exact as a float.
    #[allow(clippy::cast_precision_loss)]
    let value = (index + 1) as f32 / 8_388_608.0;
    value
}

/// The sender's end of the test: a socket, the core's sender, and when its
/// capture device captured frame 0.
struct Source {
    socket: Socket,
    sender: Sender,
    start: i64,
    to: SocketAddr,
    buffer: Vec<u8>,
    sent: u64,
}

impl Source {
    /// The raw clock when frame `index` was captured.
    fn captured(&self, index: u64) -> i64 {
        self.start
            + i64::try_from(u128::from(index) * 1_000_000_000 / u128::from(RATE)).unwrap_or(0)
    }

    /// Sends the packets whose frames have all been captured by `now`.
    fn send(&mut self, now: i64) {
        while self.captured(self.sender.next() + u64::from(PACKET)) <= now {
            let first = self.sender.next();
            let header = self.sender.packet(PACKET, self.captured(first), 0);
            let samples: Vec<f32> = (first..first + u64::from(PACKET))
                .flat_map(|index| [ramp(index), -ramp(index)])
                .collect();
            let length = write_audio(&header, &mut self.buffer).expect("room for a packet");
            to_signed24(&samples, &mut self.buffer[packet::HEADER..length]);
            self.socket
                .send_to(&self.buffer[..length], self.to, first)
                .expect("sending a packet");
            self.sent += 1;
        }
    }

    /// Answers the reports that arrived, and takes in when packets left.
    fn answer(&mut self) {
        let mut bytes = vec![0u8; 2_048];
        let mut out = [0u8; packet::ECHO];
        while let Some(received) = self.socket.receive(&mut bytes).expect("receiving") {
            let datagram = &bytes[..received.length];
            if packet::kind(datagram) != Ok(KIND_REPORT) {
                continue;
            }
            let Ok(report) = parse_report(datagram) else {
                continue;
            };
            if let Some(echo) = self.sender.answer(&report, received.arrival.time) {
                let length = write_echo(&echo, &mut out).expect("room for an answer");
                self.socket
                    .send_to(&out[..length], received.from, u64::MAX)
                    .expect("sending an answer");
            }
        }
        while let Some(departure) = self.socket.departure().expect("departures") {
            if departure.tag != u64::MAX {
                let timeline = self.sender.timeline();
                self.sender
                    .departed(timeline, departure.tag, departure.stamp.time);
            }
        }
    }
}

/// What a run of a stream gave.
struct Outcome {
    counts: NetworkCounts,
    sent: u64,
    /// The receiver's estimate of the delay of the path from the sender.
    delay: i64,
    /// How late each frame played that was measured, in seconds, sorted.
    lateness: Vec<f64>,
}

impl Outcome {
    /// The lateness that a share `share` of the frames is not later than.
    fn quantile(&self, share: f64) -> f64 {
        // A count of frames is exact as a float; the place is within the list.
        #[allow(
            clippy::cast_precision_loss,
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss
        )]
        let place = ((self.lateness.len() - 1) as f64 * share) as usize;
        self.lateness[place]
    }
}

/// Runs a stream for `seconds` from a sender to a receiver, straight or
/// through a proxy that impairs it each way as `path` says, and measures
/// the frames that play after `from` seconds.
fn run(seconds: i64, from: i64, path: Option<(Impairment, Impairment)>) -> Outcome {
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("an address");
    let receiving = Socket::bind(loopback).expect("a socket");
    let address = receiving.address().expect("its address");
    let proxy = path
        .map(|(forward, backward)| Proxy::start(address, forward, backward, 5).expect("a proxy"));
    let to = proxy.as_ref().map_or(address, Proxy::near);
    let start = clock::raw();
    let mut source = Source {
        socket: Socket::bind(loopback).expect("a socket"),
        sender: Sender::new(
            SenderSettings {
                stream: 1,
                rate: RATE,
                channels: 2,
                format: Format::Signed24,
                span: 2_000,
                window: u32::from(PACKET) * 10,
                clock: 1,
            },
            7,
            LEVEL,
        ),
        start,
        to,
        buffer: vec![0u8; 2_048],
        sent: 0,
    };

    let sizes = Sizes {
        buffers: 32,
        datagram: 2_048,
        messages: 64,
    };
    let (network_end, audio_end) = link(sizes);
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
        drift: 0,
        start: start + 7_000_000,
        lead: 4_000_000,
        hidden: 0,
    };
    let frames = usize::try_from(seconds).unwrap_or(0) * 48_000 + 1_000;
    let mut output = Output::new(device, frames);

    let end = start + seconds * 1_000_000_000;
    loop {
        let now = clock::raw();
        if now > end {
            break;
        }
        source.send(now);
        network.turn(0).expect("the network end");
        source.answer();
        output.run(now, &mut audio);
        std::thread::sleep(Duration::from_micros(500));
    }

    // How late each frame is that played after `from` seconds, read from
    // its sample.
    let mut lateness: Vec<f64> = Vec::new();
    for (count, frame) in (0u64..).zip(output.recorded().as_chunks::<CHANNELS>().0) {
        let left = output.device().played(count);
        if left < start + from * 1_000_000_000 || frame[0] == 0.0 {
            continue;
        }
        let position = f64::from(frame[0]) * 8_388_608.0 - 1.0;
        // A time on the raw clock is exact as a float to a nanosecond for
        // years.
        #[allow(clippy::cast_precision_loss)]
        let due = (left - LEVEL - start) as f64 * f64::from(RATE) * 1e-9;
        lateness.push((due - position) / f64::from(RATE));
    }
    lateness.sort_by(f64::total_cmp);
    Outcome {
        counts: network.counts(),
        sent: source.sent,
        delay: audio.playback().receiver().delay(),
        lateness,
    }
}

#[test]
fn a_stream_over_loopback_comes_out_on_time() {
    let outcome = run(3, 1, None);
    let counts = outcome.counts;
    assert_eq!(counts.dropped, 0, "{counts:?}");
    assert!(
        counts.packets + 2 >= outcome.sent,
        "{counts:?}, {} sent",
        outcome.sent
    );
    assert!(counts.reports > 10 && counts.answers > 10, "{counts:?}");
    // The delay of the loopback interface is well under a microsecond.
    assert!(
        (0..1_000).contains(&outcome.delay),
        "delay {}",
        outcome.delay
    );
    // Every clock is the same, and the stamps are the kernel's: the frames
    // play within a microsecond of when they are due.
    assert!(
        outcome.lateness.len() > 80_000,
        "{} frames",
        outcome.lateness.len()
    );
    let (early, late) = (outcome.quantile(0.0), outcome.quantile(1.0));
    assert!(early > -1e-6 && late < 1e-6, "from {early} to {late}");
}

#[test]
fn the_receiver_measures_a_path_of_two_milliseconds_and_plays_on_time() {
    let two = Impairment {
        delay: 2_000_000,
        ..Impairment::NONE
    };
    let outcome = run(6, 4, Some((two, two)));
    let counts = outcome.counts;
    assert_eq!(counts.dropped, 0, "{counts:?}");
    assert!(counts.reports > 10 && counts.answers > 10, "{counts:?}");
    // The proxy holds every datagram 2 ms and passes it on as soon as its
    // timer allows after that, which on an idle host is within a fraction of
    // a millisecond. The estimate takes the fastest datagrams of its memory.
    let delay = outcome.delay;
    assert!((2_000_000..2_200_000).contains(&delay), "delay {delay}");
    // Once the regulator has moved the 2 ms by which it first played late, a
    // frame plays early or late by what the estimate of the delay differs
    // from the fastest datagram's, which is what the proxy's timer adds to
    // either direction: tens of microseconds here.
    assert!(
        outcome.lateness.len() > 90_000,
        "{} frames",
        outcome.lateness.len()
    );
    let (early, late) = (outcome.quantile(0.02), outcome.quantile(0.98));
    assert!(early > -100e-6 && late < 100e-6, "from {early} to {late}");
}
