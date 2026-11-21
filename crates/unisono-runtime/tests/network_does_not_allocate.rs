// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The network turns of both `SenderNetwork` and `ReceiverNetwork` allocate
//! and free no memory after setup—including during adaptive `Chooser` level
//! computation, large capture gaps, multi-receiver sends, report answers,
//! retransmission requests, and `Asking` run splits.
//!
//! This file is a test binary of its own because it replaces the global
//! allocator with a counting allocator (seccomp alone does not catch
//! allocations served from glibc's pre-existing heap arena).

mod common;

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::net::{SocketAddr, UdpSocket};
use std::sync::atomic::{AtomicU64, Ordering};

use common::{CHANNELS, settings};
use unisono_core::packet::{
    self, Audio, Format, PROTECTION_ON_REQUEST, RECENT, Recent, Report, Request, write_audio,
    write_needs, write_report, write_request,
};
use unisono_core::sender::Settings as StreamSettings;
use unisono_dsp::Parameters;
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::pump::ReceiverPlayback;
use unisono_runtime::receive::{self, Intake, ReceiverAudio, ReceiverNetwork, Reporting, Sizes};
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
