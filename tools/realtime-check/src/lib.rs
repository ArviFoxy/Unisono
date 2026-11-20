// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The functions of the core that run on the real-time threads, as one
//! library.
//!
//! Nothing here is used by unisono. `tools/realtime.sh` builds this library
//! and inspects its machine code: every function below, with everything it
//! calls, must come out free of calls into the kernel, of calls to an
//! allocator, and of code that panics. The functions take and return plain
//! data, so nothing that they call can come from outside this library.

#![no_std]
// The entry points are named for the inspection, not for a caller in C.
#![allow(improper_ctypes_definitions)]

use unisono_core::device::Device;
use unisono_core::packet::{self, Audio, Echo, Rejected, Report};
use unisono_core::player::Plan;
use unisono_core::receiver::{Heard, Receiver, Segment};
use unisono_core::sender::Sender;

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
pub extern "C" fn realtime_receiver_packet(receiver: &mut Listener, header: &Audio, arrival: i64) -> Heard {
    receiver.packet(header, arrival)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_cycle(receiver: &mut Listener, time: i64, duration: i64, frames: u32) -> Plan {
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
pub extern "C" fn realtime_receiver_report(receiver: &mut Listener, stream: u16, report: &mut Report) -> bool {
    match receiver.report(stream) {
        Some(made) => {
            *report = made;
            true
        }
        None => false,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_receiver_reported(receiver: &mut Listener, sequence: u64, departure: i64) {
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
pub extern "C" fn realtime_sender_packet(sender: &mut Sender, frames: u16, capture: i64, drift: i32) -> Audio {
    sender.packet(frames, capture, drift)
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sender_departed(sender: &mut Sender, timeline: u64, index: u64, departure: i64) {
    sender.departed(timeline, index, departure);
}

#[unsafe(no_mangle)]
pub extern "C" fn realtime_sender_answer(sender: &Sender, report: &Report, arrival: i64, echo: &mut Echo) -> bool {
    match sender.answer(report, arrival) {
        Some(made) => {
            *echo = made;
            true
        }
        None => false,
    }
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
