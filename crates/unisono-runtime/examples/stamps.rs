// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Diagnostic tool measuring loopback UDP RX/TX timestamp provenance,
//! clock-conversion error bounds, and kernel vs. userspace transit latency.
//!
//! Run with `cargo run --release --example stamps -p unisono-runtime`.

use std::io;
use std::net::SocketAddr;

use unisono_runtime::clock;
use unisono_runtime::socket::Socket;

/// The middle and the largest of some numbers.
fn middle_and_largest(mut values: Vec<i64>) -> (i64, i64) {
    values.sort_unstable();
    let middle = values.get(values.len() / 2).copied().unwrap_or(0);
    (middle, values.last().copied().unwrap_or(0))
}

fn main() -> io::Result<()> {
    let loopback = SocketAddr::from(([127, 0, 0, 1], 0));
    let mut sender = Socket::bind(loopback)?;
    let mut listener = Socket::bind(loopback)?;
    let to = listener.address()?;
    let mut buffer = [0u8; 64];
    let (mut sent, mut arrived, mut left) = (Vec::new(), Vec::new(), Vec::new());
    for tag in 0..20_000u64 {
        sent.push(sender.send_to(&tag.to_le_bytes(), to, tag)?.before);
        loop {
            listener.wait(100)?;
            if let Some(received) = listener.receive(&mut buffer)? {
                arrived.push(received);
                break;
            }
        }
        while let Some(departure) = sender.departure()? {
            left.push(departure);
        }
        std::thread::sleep(std::time::Duration::from_micros(200));
    }
    println!("arrivals stamped by: {:?}", listener.arrivals());
    println!("departures stamped by: {:?}", sender.departures());
    println!("departures reported: {} of {}", left.len(), sent.len());
    let mut by_kernel = Vec::new();
    let mut by_program = Vec::new();
    let mut errors = Vec::new();
    for departure in &left {
        let Ok(number) = usize::try_from(departure.tag) else {
            continue;
        };
        let (Some(arrival), Some(before)) = (arrived.get(number), sent.get(number)) else {
            continue;
        };
        by_kernel.push(arrival.arrival.time - departure.stamp.time);
        by_program.push(arrival.read - before);
        errors.push(arrival.arrival.error.max(departure.stamp.error));
    }
    let report = |name: &str, values: Vec<i64>| {
        let (middle, largest) = middle_and_largest(values);
        println!("{name}: middle {middle} ns, largest {largest} ns");
    };
    report("stated error of a stamp", errors);
    report("transit by the kernel's stamps", by_kernel);
    report("transit by the program's stamps", by_program);
    let reading = clock::measure(100);
    println!(
        "system clock minus raw clock: {} ns, measured to within {} ns",
        reading.offset, reading.error
    );
    Ok(())
}
