// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Two-thread receiver integration tests over real loopback UDP sockets and
//! `CLOCK_MONOTONIC_RAW`.
//!
//! Sends a ramp signal `(i + 1) / 2^23` over loopback and drives a virtual
//! playback device from the receiver's audio end, verifying end-to-end
//! latency and path-delay measurement.

mod common;

use std::net::SocketAddr;
use std::time::Duration;

use common::{CHANNELS, peer_settings, settings};
use unisono_core::packet::{self, Format, KIND_REPORT, parse_report, write_audio, write_echo};
use unisono_core::player::ModalRegulation;
use unisono_core::sender::{Sender, Settings as SenderSettings};
use unisono_core::sync::WEIGHT_UNITY_Q16;
use unisono_dsp::Parameters;
use unisono_dsp::format::to_signed24;
use unisono_runtime::clock;
use unisono_runtime::network_thread::NetworkThread;
use unisono_runtime::proxy::{Impairment, Proxy};
use unisono_runtime::pump::ReceiverPlayback;
use unisono_runtime::receive::{
    Intake, NetConfig, NetworkCounts, PeerConfig, ReceiverAudio, ReceiverNetwork, Reporting, Sizes,
    link,
};
use unisono_runtime::send::{self, SenderNetwork, Settings as SendSettings};
use unisono_runtime::socket::Socket;
use unisono_runtime::virtual_device::{Device, Input, Output};

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
            let departure = clock::raw().max(received.arrival.time);
            if let Some(echo) = self
                .sender
                .answer(&report, received.arrival.time, departure)
            {
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
    // Keep the clock-estimator span at least as long as the run so `Answers`
    // does not evaluate the lower-hull line far outside its fitted interval,
    // which otherwise amplifies host timer-jitter slope into spurious path
    // underestimation on busy runners.
    let span = u32::try_from(seconds.saturating_mul(1_000))
        .unwrap_or(2_000)
        .max(2_000);
    let mut source = Source {
        socket: Socket::bind(loopback).expect("a socket"),
        sender: Sender::new(
            SenderSettings {
                stream: 1,
                rate: RATE,
                channels: 2,
                format: Format::Signed24,
                span,
                window: u32::from(PACKET) * 20,
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
            reports: Some(Reporting::USUAL),
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
    // a millisecond (and can overshoot by a few hundred microseconds on a busy
    // VM). The estimate evaluates the fastest kept answers against the clock's
    // lower-hull line, so small boundary slope error can pull it slightly
    // below 2 ms.
    let delay = outcome.delay;
    assert!((1_900_000..2_500_000).contains(&delay), "delay {delay}");
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

#[test]
#[allow(clippy::too_many_lines)]
fn star_sync_over_proxy_under_seccomp_measures_path_and_plays_on_time() {
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
    let rx_socket = Socket::bind(loopback).expect("rx socket");
    let rx_addr = rx_socket.address().expect("rx addr");
    let two = Impairment {
        delay: 2_000_000,
        ..Impairment::NONE
    };
    let proxy = Proxy::start(rx_addr, two, two, 11).expect("proxy");
    let start = clock::raw();

    let (mut capture_end, sender_end) = send::link(16, 256, CHANNELS);
    let sender_net = SenderNetwork::new(
        Socket::bind(loopback).expect("tx socket"),
        sender_end,
        SendSettings {
            stream: SenderSettings {
                stream: 1,
                rate: RATE,
                channels: 2,
                format: Format::Signed24,
                span: 2_000,
                window: u32::from(PACKET) * 10,
                clock: 1,
            },
            packet: PACKET,
            level: LEVEL,
            choice: None,
            timeline: 7,
            receivers: vec![proxy.near()],
            kept: 0,
        },
    );
    let tx_thread = NetworkThread::spawn("test-star-tx", sender_net, 2).expect("tx thread");

    let sizes = Sizes {
        buffers: 32,
        datagram: 2_048,
        messages: 64,
    };
    let (net_end, audio_end) = link(sizes);
    let net_cfg = NetConfig::peer(1, 1, sizes.datagram);
    assert!(net_cfg.validate().is_ok());
    let rx_net = ReceiverNetwork::with_config(rx_socket, net_end, &net_cfg);
    let rx_thread = NetworkThread::spawn("test-star-rx", rx_net, 2).expect("rx thread");
    #[cfg(target_os = "linux")]
    assert!(
        rx_thread.restricted(),
        "receiver network thread should be seccomp-restricted on Linux"
    );

    let playback: ReceiverPlayback<64, 64, 8, 64> = ReceiverPlayback::new(&peer_settings(
        RATE,
        Parameters::for_rate(RATE),
        1,
        ModalRegulation::lipsync(1_000_000, 240),
    ));
    let mut audio = ReceiverAudio::new(
        playback,
        audio_end,
        Intake {
            items: 16,
            reports: Some(Reporting::USUAL),
        },
    );
    let mut input = Input::new(
        Device {
            rate: RATE,
            channels: CHANNELS,
            cycle: 256,
            drift: 0,
            start,
            lead: 1_000_000,
            hidden: 0,
        },
        |position, _, frame: &mut [f32]| {
            frame[0] = ramp(position);
            frame[1] = -ramp(position);
        },
    );
    let mut output = Output::new(
        Device {
            rate: RATE,
            channels: CHANNELS,
            cycle: 256,
            drift: 0,
            start: start + 7_000_000,
            lead: 4_000_000,
            hidden: 0,
        },
        5 * 48_000 + 1_000,
    );

    let end = start + 4_000_000_000;
    loop {
        let now = clock::raw();
        if now > end {
            break;
        }
        input.run(now, &mut capture_end);
        output.run(now, &mut audio);
        std::thread::sleep(Duration::from_micros(500));
    }

    let rx_stopped = rx_thread.stop().expect("stop rx");
    let tx_stopped = tx_thread.stop().expect("stop tx");
    assert!(rx_stopped.error.is_none(), "{:?}", rx_stopped.error);
    assert!(tx_stopped.error.is_none(), "{:?}", tx_stopped.error);

    let counts = rx_stopped.network.counts();
    assert_eq!(counts.dropped, 0, "{counts:?}");
    assert_eq!(
        counts.peer_probes_sent, 0,
        "star mode sends zero peer probes"
    );
    assert!(counts.answers > 10, "{counts:?}");
    let snap = rx_stopped
        .network
        .sync_snapshot()
        .expect("peer/star snapshot");
    assert!(snap.valid, "{snap:?}");
    assert!(!snap.peer_active, "0 peers must stay in Star mode");
    let delay = audio.playback().receiver().delay();
    assert!(
        (1_950_000..2_500_000).contains(&delay),
        "star proxy delay={delay}"
    );

    let mut lateness: Vec<f64> = Vec::new();
    for (count, frame) in (0u64..).zip(output.recorded().as_chunks::<CHANNELS>().0) {
        let left = output.device().played(count);
        if left < start + 2_000_000_000 || frame[0] == 0.0 {
            continue;
        }
        let position = f64::from(frame[0]) * 8_388_608.0 - 1.0;
        #[allow(clippy::cast_precision_loss)]
        let due = (left - LEVEL - start) as f64 * f64::from(RATE) * 1e-9;
        lateness.push((due - position) / f64::from(RATE));
    }
    lateness.sort_by(f64::total_cmp);
    assert!(lateness.len() > 80_000, "{} frames", lateness.len());
    let low = lateness[lateness.len() / 50];
    let high = lateness[lateness.len() * 49 / 50];
    assert!(low > -150e-6 && high < 150e-6, "from {low} to {high}");
}

#[test]
#[allow(clippy::too_many_lines)]
fn two_peer_receivers_under_seccomp_exchange_probes_relays_and_align() {
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
    let rx1_sock = Socket::bind(loopback).expect("rx1");
    let rx2_sock = Socket::bind(loopback).expect("rx2");
    let rx1_addr = rx1_sock.address().expect("rx1 addr");
    let rx2_addr = rx2_sock.address().expect("rx2 addr");

    let two_ms = Impairment {
        delay: 2_000_000,
        ..Impairment::NONE
    };
    let proxy1 = Proxy::start(rx1_addr, two_ms, two_ms, 31).expect("proxy1");
    let proxy2 = Proxy::start(rx2_addr, two_ms, two_ms, 32).expect("proxy2");
    let start = clock::raw();

    let (mut capture_end, sender_end) = send::link(16, 256, CHANNELS);
    let sender_net = SenderNetwork::new(
        Socket::bind(loopback).expect("tx"),
        sender_end,
        SendSettings {
            stream: SenderSettings {
                stream: 1,
                rate: RATE,
                channels: 2,
                format: Format::Signed24,
                span: 2_000,
                window: u32::from(PACKET) * 10,
                clock: 1,
            },
            packet: PACKET,
            level: LEVEL,
            choice: None,
            timeline: 9,
            receivers: vec![proxy1.near(), proxy2.near()],
            kept: 0,
        },
    );
    let tx_thread = NetworkThread::spawn("test-peer-tx", sender_net, 2).expect("tx thread");

    let sizes = Sizes {
        buffers: 32,
        datagram: 2_048,
        messages: 64,
    };
    let (net1_end, audio1_end) = link(sizes);
    let (net2_end, audio2_end) = link(sizes);

    let mut cfg1 = NetConfig::peer(1, 1, sizes.datagram);
    cfg1.peers.push(PeerConfig {
        identity: 2,
        address: rx2_addr,
        weight_q16: WEIGHT_UNITY_Q16,
    });
    assert!(cfg1.validate().is_ok());
    let mut cfg2 = NetConfig::peer(1, 2, sizes.datagram);
    cfg2.peers.push(PeerConfig {
        identity: 1,
        address: rx1_addr,
        weight_q16: WEIGHT_UNITY_Q16,
    });
    assert!(cfg2.validate().is_ok());

    let rx1_thread = NetworkThread::spawn(
        "test-peer-rx1",
        ReceiverNetwork::with_config(rx1_sock, net1_end, &cfg1),
        2,
    )
    .expect("rx1 thread");
    let rx2_thread = NetworkThread::spawn(
        "test-peer-rx2",
        ReceiverNetwork::with_config(rx2_sock, net2_end, &cfg2),
        2,
    )
    .expect("rx2 thread");
    #[cfg(target_os = "linux")]
    {
        assert!(rx1_thread.restricted());
        assert!(rx2_thread.restricted());
    }

    let modal = ModalRegulation::lipsync(1_000_000, 240);
    let mut audio1 = ReceiverAudio::new(
        ReceiverPlayback::<64, 64, 8, 64>::new(&peer_settings(
            RATE,
            Parameters::for_rate(RATE),
            1,
            modal,
        )),
        audio1_end,
        Intake {
            items: 16,
            reports: Some(Reporting::USUAL),
        },
    );
    let mut audio2 = ReceiverAudio::new(
        ReceiverPlayback::<64, 64, 8, 64>::new(&peer_settings(
            RATE,
            Parameters::for_rate(RATE),
            2,
            modal,
        )),
        audio2_end,
        Intake {
            items: 16,
            reports: Some(Reporting::USUAL),
        },
    );

    let mut input = Input::new(
        Device {
            rate: RATE,
            channels: CHANNELS,
            cycle: 256,
            drift: 0,
            start,
            lead: 1_000_000,
            hidden: 0,
        },
        |position, _, frame: &mut [f32]| {
            frame[0] = ramp(position);
            frame[1] = -ramp(position);
        },
    );
    let mut out1 = Output::new(
        Device {
            rate: RATE,
            channels: CHANNELS,
            cycle: 256,
            drift: 0,
            start: start + 7_000_000,
            lead: 4_000_000,
            hidden: 0,
        },
        7 * 48_000 + 1_000,
    );
    let mut out2 = Output::new(
        Device {
            rate: RATE,
            channels: CHANNELS,
            cycle: 256,
            drift: 0,
            start: start + 7_500_000,
            lead: 4_000_000,
            hidden: 0,
        },
        7 * 48_000 + 1_000,
    );

    // Run 6 s so common mode (`common_gain = 0.5 / s`, time constant 2 s)
    // settles after the initial proxy path lock, then inspect the last 2 s.
    let end = start + 6_000_000_000;
    loop {
        let now = clock::raw();
        if now > end {
            break;
        }
        input.run(now, &mut capture_end);
        out1.run(now, &mut audio1);
        out2.run(now, &mut audio2);
        std::thread::sleep(Duration::from_micros(500));
    }

    let s1 = rx1_thread.stop().expect("stop rx1");
    let s2 = rx2_thread.stop().expect("stop rx2");
    let tx_s = tx_thread.stop().expect("stop tx");
    assert!(s1.error.is_none(), "{:?}", s1.error);
    assert!(s2.error.is_none(), "{:?}", s2.error);
    assert!(tx_s.error.is_none(), "{:?}", tx_s.error);

    for (label, stopped) in [("rx1", &s1), ("rx2", &s2)] {
        let c = stopped.network.counts();
        assert_eq!(c.dropped, 0, "{label}: {c:?}");
        assert!(c.peer_probes_sent > 5, "{label}: {c:?}");
        assert!(c.peer_probes_answered > 5, "{label}: {c:?}");
        assert!(c.peer_echoes_received > 5, "{label}: {c:?}");
        assert!(c.peer_relays_sent > 2, "{label}: {c:?}");
        assert!(c.peer_relays_received > 2, "{label}: {c:?}");
        let snap = stopped.network.sync_snapshot().expect("snapshot");
        assert!(
            snap.valid && snap.peer_active && snap.active_peers == 1,
            "{label}: {snap:?}"
        );
    }

    // Both receivers decode clean on-time ramp frames in the last two seconds,
    // and their relative inter-receiver alignment is tightly locked.
    let mut medians = [0.0f64; 2];
    for (idx, (label, output)) in [("rx1", &out1), ("rx2", &out2)].into_iter().enumerate() {
        let mut lateness: Vec<f64> = Vec::new();
        for (count, frame) in (0u64..).zip(output.recorded().as_chunks::<CHANNELS>().0) {
            let left = output.device().played(count);
            if left < start + 4_000_000_000 || frame[0] == 0.0 {
                continue;
            }
            let position = f64::from(frame[0]) * 8_388_608.0 - 1.0;
            #[allow(clippy::cast_precision_loss)]
            let due = (left - LEVEL - start) as f64 * f64::from(RATE) * 1e-9;
            lateness.push((due - position) / f64::from(RATE));
        }
        lateness.sort_by(f64::total_cmp);
        assert!(
            lateness.len() > 80_000,
            "{label}: {} frames",
            lateness.len()
        );
        medians[idx] = lateness[lateness.len() / 2];
        let low = lateness[lateness.len() / 50];
        let high = lateness[lateness.len() * 49 / 50];
        assert!(
            low > -150e-6 && high < 150e-6,
            "{label}: from {low} to {high}"
        );
    }
    let inter_receiver = (medians[0] - medians[1]).abs();
    assert!(
        inter_receiver < 50e-6,
        "inter-receiver differential error too large: {inter_receiver} s (medians={medians:?})"
    );
}
