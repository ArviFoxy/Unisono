// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Exported `cdylib` wrappers for `unisono_core` real-time entry points
//! audited by `tools/realtime.sh`.
//!
//! Not linked into `unisono` binaries; compiled solely so `reachable` can
//! verify that every exported function and its transitive callees are free of
//! syscalls, allocator calls, and panic paths.

#![no_std]
// The entry points are named for the inspection, not for a caller in C.
#![allow(improper_ctypes_definitions)]

use unisono_core::device::Device;
use unisono_core::packet::{self, Audio, Echo, PeerEcho, PeerProbe, PeerRelay, Rejected, Report};
use unisono_core::player::{ModalRegulation, Plan};
use unisono_core::receiver::{Heard, Receiver, Segment};
use unisono_core::sender::Sender;
use unisono_core::sync::{Sync, SyncSnapshot};

/// A receiver of the sizes that a program would use.
type Listener = Receiver<64, 64, 8>;

unsafe extern "C" {
    /// Never defined: if any panic path survives dead-code elimination, the
    /// linker leaves this symbol undefined and `tools/realtime.sh` fails.
    fn unisono_realtime_code_panicked() -> !;
}

/// The handler of a panic. No function below may reach it; calling an
/// undefined external symbol prevents the compiler from silently folding a
/// panic path into an infinite loop and lets the inspection catch it by name.
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    // SAFETY: never called in a valid build; exists solely as a link-time trap.
    unsafe { unisono_realtime_code_panicked() }
}

/// An intentionally panicking entry point built only under `panic-probe`, so
/// `tools/realtime.sh` can confirm that the link-time panic trap fires.
#[cfg(feature = "panic-probe")]
#[unsafe(no_mangle)]
pub extern "C" fn realtime_panic_probe(fail: bool) {
    assert!(!fail);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_packet(
    receiver: &mut Listener,
    header: &Audio,
    arrival: i64,
) -> Heard {
    receiver.packet(header, arrival)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_cycle(
    receiver: &mut Listener,
    time: i64,
    duration: i64,
    frames: u32,
) -> Plan {
    receiver.cycle(time, duration, frames)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_take(receiver: &mut Listener, limit: u32) -> Segment {
    receiver.take(limit)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_skip(receiver: &mut Listener, to: u64) -> u64 {
    receiver.skip(to)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_report(receiver: &mut Listener, report: &mut Report) -> bool {
    match receiver.report() {
        Some(made) => {
            *report = made;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_reported(
    receiver: &mut Listener,
    sequence: u64,
    departure: i64,
) {
    receiver.reported(sequence, departure);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_echo(receiver: &mut Listener, echo: &Echo) {
    receiver.echo(echo);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_device_observe(device: &mut Device<64>, position: u64, time: i64) {
    device.observe(position, time);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_device_when(device: &Device<64>, position: u64, time: &mut i64) -> bool {
    match device.when(position) {
        Some(found) => {
            *time = found;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_device_when_cycle(
    device: &Device<64>,
    position: u64,
    frames: u32,
    start: &mut i64,
    duration_q16: &mut i64,
) -> bool {
    match device.when_cycle(position, frames) {
        Some((s, d)) => {
            *start = s;
            *duration_q16 = d;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sender_packet(
    sender: &mut Sender,
    frames: u16,
    capture: i64,
    drift: i32,
) -> Audio {
    sender.packet(frames, capture, drift)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sender_departed(
    sender: &mut Sender,
    timeline: u64,
    index: u64,
    departure: i64,
) {
    sender.departed(timeline, index, departure);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sender_answer(
    sender: &Sender,
    report: &Report,
    arrival: i64,
    departure: i64,
    echo: &mut Echo,
) -> bool {
    match sender.answer(report, arrival, departure) {
        Some(made) => {
            *echo = made;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_enable_sync(
    receiver: &mut Listener,
    regulation: ModalRegulation,
) {
    receiver.enable_sync(regulation);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_apply_sync(receiver: &mut Listener, snapshot: SyncSnapshot) {
    receiver.apply_sync(snapshot);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sync_on_sender_echo(sync: &mut Sync, echo: &Echo, arrival: i64) -> bool {
    sync.on_sender_echo(echo, arrival)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sync_on_peer_probe(
    sync: &Sync,
    probe: &PeerProbe,
    arrival: i64,
    departure: i64,
    echo: &mut PeerEcho,
) -> bool {
    match sync.on_peer_probe(probe, arrival, departure) {
        Some(made) => {
            *echo = made;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sync_on_peer_echo(
    sync: &mut Sync,
    echo: &PeerEcho,
    arrival: i64,
) -> bool {
    sync.on_peer_echo(echo, arrival)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sync_on_peer_relay(
    sync: &mut Sync,
    relay: &PeerRelay,
    arrival: i64,
) -> usize {
    sync.on_peer_relay(relay, arrival)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sync_build_relay(
    sync: &mut Sync,
    now_ns: i64,
    relay: &mut PeerRelay,
) -> bool {
    match sync.build_relay(now_ns) {
        Some(made) => {
            *relay = made;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sync_step(sync: &mut Sync, now_ns: i64) -> SyncSnapshot {
    sync.step(now_ns)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_parse_audio(bytes: &[u8], header: &mut Audio) -> bool {
    match packet::parse_audio(bytes) {
        Ok(read) => {
            *header = read;
            true
        }
        Err(_) => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_write_audio(header: &Audio, bytes: &mut [u8]) -> usize {
    packet::write_audio(header, bytes).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_kind(bytes: &[u8]) -> u8 {
    match packet::kind(bytes) {
        Ok(kind) => kind,
        Err(Rejected::Kind(kind)) => kind,
        Err(_) => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_parse_report(bytes: &[u8], report: &mut Report) -> bool {
    match packet::parse_report(bytes) {
        Ok(read) => {
            *report = read;
            true
        }
        Err(_) => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_write_report(report: &Report, bytes: &mut [u8], length: usize) -> usize {
    packet::write_report(report, bytes, length).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_parse_echo(bytes: &[u8], echo: &mut Echo) -> bool {
    match packet::parse_echo(bytes) {
        Ok(read) => {
            *echo = read;
            true
        }
        Err(_) => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_write_echo(echo: &Echo, bytes: &mut [u8]) -> usize {
    packet::write_echo(echo, bytes).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_parse_peer_probe(bytes: &[u8], probe: &mut PeerProbe) -> bool {
    match packet::parse_peer_probe(bytes) {
        Ok(read) => {
            *probe = read;
            true
        }
        Err(_) => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_write_peer_probe(probe: &PeerProbe, bytes: &mut [u8]) -> usize {
    packet::write_peer_probe(probe, bytes).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_parse_peer_echo(bytes: &[u8], echo: &mut PeerEcho) -> bool {
    match packet::parse_peer_echo(bytes) {
        Ok(read) => {
            *echo = read;
            true
        }
        Err(_) => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_write_peer_echo(echo: &PeerEcho, bytes: &mut [u8]) -> usize {
    packet::write_peer_echo(echo, bytes).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_parse_peer_relay(bytes: &[u8], relay: &mut PeerRelay) -> bool {
    match packet::parse_peer_relay(bytes) {
        Ok(read) => {
            *relay = read;
            true
        }
        Err(_) => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_write_peer_relay(relay: &PeerRelay, bytes: &mut [u8]) -> usize {
    packet::write_peer_relay(relay, bytes).unwrap_or(0)
}
