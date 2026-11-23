// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Verifies that `SenderNetwork` and `ReceiverNetwork` turns allocate and
//! free zero heap memory after setup, including during adaptive `Chooser`
//! level computation, large capture gaps, multi-receiver sends, report echoes,
//! retransmission requests, and `RetransmissionTracker` gap splits.
//!
//! This file is a test binary of its own because it replaces the global
//! allocator with a counting allocator (seccomp alone does not catch
//! allocations served from glibc's pre-existing heap arena).

mod common;

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::net::{SocketAddr, UdpSocket};
use std::sync::atomic::{AtomicU64, Ordering};

use common::{CHANNELS, peer_settings, settings};
use unisono_core::packet::{
    self, Audio, Echo, Format, PROTECTION_ON_REQUEST, PeerEcho, PeerProbe, PeerRelay, RECENT,
    Recent, RelayEdge, Report, Request, write_audio, write_echo, write_needs, write_peer_echo,
    write_peer_probe, write_peer_relay, write_report, write_request,
};
use unisono_core::player::ModalRegulation;
use unisono_core::sender::Settings as StreamSettings;
use unisono_core::sync::WEIGHT_UNITY_Q16;
use unisono_dsp::Parameters;
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::pump::ReceiverPlayback;
use unisono_runtime::receive::{
    self, Intake, NetConfig, PeerConfig, ReceiverAudio, ReceiverNetwork, Reporting, Sizes,
};
use unisono_runtime::send::{self, SenderNetwork, Settings as SenderSettings};
use unisono_runtime::socket::Socket;

thread_local! {
    static COUNTED: Cell<bool> = const { Cell::new(false) };
}

static CALLS: AtomicU64 = AtomicU64::new(0);

struct Counting;

impl Counting {
    fn count() {
        if COUNTED.try_with(Cell::get).unwrap_or(false) {
            CALLS.fetch_add(1, Ordering::Relaxed);
        }
    }
}

// SAFETY: forwards every call unmodified to `System` and only touches a
// thread-local flag and an atomic counter.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Self::count();
        // SAFETY: caller upholds `GlobalAlloc::alloc`.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        Self::count();
        // SAFETY: caller upholds `GlobalAlloc::dealloc`.
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        Self::count();
        // SAFETY: caller upholds `GlobalAlloc::realloc`.
        unsafe { System.realloc(pointer, layout, size) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn calls_during(work: impl FnOnce()) -> u64 {
    let before = CALLS.load(Ordering::Relaxed);
    COUNTED.set(true);
    work();
    COUNTED.set(false);
    CALLS.load(Ordering::Relaxed) - before
}

#[test]
fn sender_network_turn_allocates_nothing_with_chooser_gaps_and_multiple_receivers() {
    const RATE: u32 = 48_000;
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
    let r1 = UdpSocket::bind(loopback).expect("r1");
    let r2 = UdpSocket::bind(loopback).expect("r2");
    r1.set_nonblocking(true).expect("nb");
    r2.set_nonblocking(true).expect("nb");
    let r1_addr = r1.local_addr().expect("r1 addr");
    let r2_addr = r2.local_addr().expect("r2 addr");

    let sender_socket = Socket::bind(loopback).expect("sender socket");
    let sender_addr = sender_socket.address().expect("sender addr");
    let (mut capture_end, sender_end) = send::link(8, 256, CHANNELS);
    let choice = Choice {
        weights: Weights {
            latency: 1_000.0,
            target: 0,
            off_target: 0.0,
            gap: 600.0,
            missed: 60_000.0,
            moving: 60.0,
        },
        history: 2_400,
        slope: 1_000_000,
    };
    let mut sender = SenderNetwork::new(
        sender_socket,
        sender_end,
        SenderSettings {
            stream: StreamSettings {
                stream: 1,
                rate: RATE,
                channels: 2,
                format: Format::Signed24,
                span: 2_000,
                window: 240,
                clock: 1,
            },
            packet: 240,
            level: 30_000_000,
            choice: Some(choice),
            timeline: 7,
            receivers: vec![r1_addr, r2_addr],
            kept: 32,
        },
    );

    let samples = [0.25f32; 512];
    let mut report_buf = [0u8; 160];
    let mut req_buf = [0u8; packet::REQUEST];
    let mut sink = [0u8; 2_048];
    let mut calls = 0u64;

    // Run enough cycles (>1 s = 200+ packets) to exercise:
    // - packet framing across cycle boundaries
    // - multi-receiver sends (tagged + untagged)
    // - adaptive Chooser observation and `choose()` sorting (`sort_unstable_by`)
    // - retransmission requests (`again`)
    // - a large dropped-cycle silence gap (10,000 frames)
    let mut position = 0u64;
    for step in 0..220u64 {
        if step == 50 {
            position += 10_000;
        }
        let time = i64::try_from(position * 1_000_000_000 / u64::from(RATE)).unwrap_or(0);
        capture_end.cycle(&samples, position, time);
        position += 256;

        if step > 2 && step % 4 == 0 {
            let newest = (sender.sender().next().saturating_sub(1)) / 240;
            let report = Report {
                stream: 1,
                timeline: 7,
                receiver: 1,
                sequence: step,
            };
            let mut recent = Recent::NONE;
            recent.count = u8::try_from(RECENT).expect("recent");
            recent.newest = newest;
            for (back, slot) in recent.needs.iter_mut().enumerate() {
                *slot = 5_000 + i32::try_from((step + back as u64) % 500).unwrap_or(0);
            }
            let report_cap = report_buf.len();
            let len = write_report(&report, &mut report_buf, report_cap).expect("report");
            assert!(write_needs(&recent, &mut report_buf[..len]));
            let _ = r1.send_to(&report_buf[..len], sender_addr);
        }
        if step == 100 {
            let req = Request {
                stream: 1,
                timeline: 7,
                first: sender.sender().next().saturating_sub(960),
                frames: 480,
            };
            let len = write_request(&req, &mut req_buf).expect("req");
            let _ = r1.send_to(&req_buf[..len], sender_addr);
        }

        calls += calls_during(|| {
            sender.turn(0).expect("sender turn");
        });

        while r1.recv(&mut sink).is_ok() {}
        while r2.recv(&mut sink).is_ok() {}
    }

    assert_eq!(
        calls, 0,
        "SenderNetwork::turn called allocator {calls} times"
    );
    assert!(sender.counts().packets > 200);
    assert_eq!(sender.counts().filled, 10_000);
    assert!(sender.counts().answers > 10);
    assert!(sender.counts().again > 0);
}

#[test]
fn receiver_network_turn_allocates_nothing_with_asking_splits_and_reports() {
    const RATE: u32 = 48_000;
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
    let rx_socket = Socket::bind(loopback).expect("rx socket");
    let rx_addr = rx_socket.address().expect("rx addr");
    let tx = UdpSocket::bind(loopback).expect("tx");
    tx.set_nonblocking(true).expect("nb");

    let sizes = Sizes {
        buffers: 32,
        datagram: 2_048,
        messages: 32,
    };
    let (net_end, audio_end) = receive::link(sizes);
    let mut net = ReceiverNetwork::new(rx_socket, net_end, 1, sizes);
    let playback: ReceiverPlayback<64, 64, 8, 64> =
        ReceiverPlayback::new(&settings(RATE, Parameters::for_rate(RATE)));
    let mut audio = ReceiverAudio::new(
        playback,
        audio_end,
        Intake {
            items: 16,
            reports: Some(Reporting::USUAL),
        },
    );

    // Pre-build audio datagrams outside the counted region, including an
    // out-of-order interior-split sequence (0, 960, 480, 240, 720, ...).
    let mut order = vec![0u64, 960, 480, 240, 720];
    for idx in 5..40u64 {
        order.push(idx * 240);
    }
    let datagrams: Vec<Vec<u8>> = order
        .into_iter()
        .map(|index| {
            let header = Audio {
                stream: 1,
                timeline: 7,
                index,
                capture: i64::try_from(index * 1_000_000_000 / u64::from(RATE)).unwrap_or(0),
                rate: RATE,
                frames: 240,
                channels: 2,
                format: Format::Signed24,
                level: 30_000_000,
                level_slope: 0,
                span: 2_000,
                window: 2_400,
                flags: 0,
                protection: PROTECTION_ON_REQUEST,
                stamped_index: 0,
                stamped_departure: 0,
                drift: 0,
                clock: 1,
            };
            let mut buf = vec![0u8; packet::HEADER + 240 * 2 * 3];
            let len = write_audio(&header, &mut buf).expect("write audio");
            buf.truncate(len);
            buf
        })
        .collect();

    let mut out = [0.0f32; 512];
    let mut sink = [0u8; 2_048];
    let mut calls = 0u64;
    for (step, pkt) in datagrams.iter().enumerate() {
        let _ = tx.send_to(pkt, rx_addr);
        calls += calls_during(|| {
            net.turn(0).expect("receiver turn");
        });
        let time = i64::try_from(step as u64 * 5_000_000 + 10_000_000).unwrap_or(0);
        calls += calls_during(|| {
            audio.cycle(&mut out, step as u64 * 256, time);
        });
        while tx.recv(&mut sink).is_ok() {}
    }
    calls += calls_during(|| {
        net.turn(0).expect("final receiver turn");
    });

    assert_eq!(
        calls, 0,
        "ReceiverNetwork::turn / ReceiverAudio::cycle called allocator {calls} times"
    );
    assert_eq!(net.counts().packets, datagrams.len() as u64);
    assert!(net.counts().reports > 0);
    assert!(net.counts().requests > 0);
}

#[test]
#[allow(clippy::too_many_lines)]
fn receiver_network_peer_sync_turn_allocates_nothing() {
    const RATE: u32 = 48_000;
    let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
    let rx_socket = Socket::bind(loopback).expect("rx socket");
    let rx_addr = rx_socket.address().expect("rx addr");
    let tx = UdpSocket::bind(loopback).expect("tx");
    let peer = UdpSocket::bind(loopback).expect("peer");
    tx.set_nonblocking(true).expect("nb");
    peer.set_nonblocking(true).expect("nb");
    let peer_addr = peer.local_addr().expect("peer addr");

    let sizes = Sizes {
        buffers: 32,
        datagram: 2_048,
        messages: 64,
    };
    let (net_end, audio_end) = receive::link(sizes);
    let mut cfg = NetConfig::peer(1, 1, sizes.datagram);
    cfg.peers.push(PeerConfig {
        identity: 2,
        address: peer_addr,
        weight_q16: WEIGHT_UNITY_Q16,
    });
    assert!(cfg.validate().is_ok());
    let mut net = ReceiverNetwork::with_config(rx_socket, net_end, &cfg);
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

    let datagrams: Vec<Vec<u8>> = (0..32u64)
        .map(|k| {
            let index = k * 240;
            let header = Audio {
                stream: 1,
                timeline: 7,
                index,
                capture: i64::try_from(index * 1_000_000_000 / u64::from(RATE)).unwrap_or(0),
                rate: RATE,
                frames: 240,
                channels: 2,
                format: Format::Signed24,
                level: 30_000_000,
                level_slope: 0,
                span: 2_000,
                window: 2_400,
                flags: 0,
                protection: PROTECTION_ON_REQUEST,
                stamped_index: 0,
                stamped_departure: 0,
                drift: 0,
                clock: 1,
            };
            let mut buf = vec![0u8; packet::HEADER + 240 * 2 * 3];
            let len = write_audio(&header, &mut buf).expect("write audio");
            buf.truncate(len);
            buf
        })
        .collect();

    let mut peer_probe_buf = [0u8; packet::PEER_PROBE];
    let probe_len = write_peer_probe(
        &PeerProbe {
            stream: 1,
            prober: 2,
            target: 1,
            sequence: 1,
        },
        &mut peer_probe_buf,
    )
    .expect("probe");

    let mut relay = PeerRelay::EMPTY;
    relay.stream = 1;
    relay.sender = 2;
    relay.sequence = 1;
    relay.count = 1;
    relay.edges[0] = RelayEdge {
        from_id: 0,
        to_id: 2,
        offset_ns: 100,
        variance_ns2: 25_000_000,
        age_ns: 1_000_000,
    };
    let mut relay_buf = [0u8; packet::PEER_RELAY_MAX];
    let relay_len = write_peer_relay(&relay, &mut relay_buf).expect("relay");

    let mut out = [0.0f32; 512];
    let mut recv_buf = [0u8; 2_048];
    let mut echo_buf = [0u8; packet::ECHO];
    let mut peer_echo_buf = [0u8; packet::PEER_ECHO];
    let mut calls = 0u64;

    for (step, pkt) in datagrams.iter().enumerate() {
        let _ = tx.send_to(pkt, rx_addr);
        if step == 2 {
            let _ = peer.send_to(&peer_probe_buf[..probe_len], rx_addr);
            let _ = peer.send_to(&relay_buf[..relay_len], rx_addr);
        }
        calls += calls_during(|| {
            net.turn(0).expect("receiver turn");
        });
        let now = unisono_runtime::clock::raw();
        let time = i64::try_from(step as u64 * 5_000_000 + 10_000_000).unwrap_or(0);
        calls += calls_during(|| {
            audio.cycle(&mut out, step as u64 * 256, time);
        });
        // Answer any report sent to `tx` with a v2 Echo.
        while let Ok(n) = tx.recv(&mut recv_buf) {
            if let Ok(report) = packet::parse_report(&recv_buf[..n])
                && let Some(len) = write_echo(
                    &Echo {
                        stream: report.stream,
                        receiver: report.receiver,
                        sequence: report.sequence,
                        arrival: now,
                        departure: now,
                    },
                    &mut echo_buf,
                )
            {
                let _ = tx.send_to(&echo_buf[..len], rx_addr);
            }
        }
        // Answer any PeerProbe sent to `peer` with a PeerEcho.
        while let Ok(n) = peer.recv(&mut recv_buf) {
            if let Ok(probe) = packet::parse_peer_probe(&recv_buf[..n])
                && let Some(len) = write_peer_echo(
                    &PeerEcho {
                        stream: probe.stream,
                        prober: probe.prober,
                        responder: probe.target,
                        sequence: probe.sequence,
                        arrival: now,
                        departure: now,
                    },
                    &mut peer_echo_buf,
                )
            {
                let _ = peer.send_to(&peer_echo_buf[..len], rx_addr);
            }
        }
    }
    calls += calls_during(|| {
        net.turn(0).expect("final receiver turn");
    });

    assert_eq!(
        calls, 0,
        "peer-sync ReceiverNetwork::turn / ReceiverAudio::cycle called allocator {calls} times"
    );
    assert!(net.counts().peer_probes_sent > 0);
    assert!(net.counts().peer_probes_answered > 0);
    assert!(net.counts().peer_echoes_received > 0);
    assert!(net.counts().peer_relays_received > 0);
    assert!(net.counts().answers > 0);
    assert!(net.sync_snapshot().is_some_and(|s| s.valid));
}
