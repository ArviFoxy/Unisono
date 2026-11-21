// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `unisono send`: a software capture device that makes a signal, and a
//! sender that sends what it captures.

use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use unisono_core::packet::Format;
use unisono_core::sender::Settings as StreamSettings;
use unisono_runtime::send::{self, SenderCounts, SenderNetwork, Settings};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Input};
use unisono_runtime::{clock, memory};

use crate::exported::{Metrics, Tally};
use crate::options::{Options, Wrong};
use crate::{Signal, sleep_until};

/// The options of `unisono send`.
pub(crate) const OPTIONS: &[&str] = &[
    "to",
    "bind",
    "stream",
    "rate",
    "channels",
    "bits",
    "packet",
    "level",
    "signal",
    "cycle",
    "drift",
    "span",
    "window",
    "seconds",
    "metrics",
    "clock-offset",
    "clock-skew",
];

pub(crate) const HELP: &str = "\
unisono send --to ADDRESS [--to ADDRESS ...] [options]

Captures a signal with a software device and sends it to each receiver.

  --to ADDRESS        a receiver; may be given more than once
  --bind ADDRESS      where to send from (0.0.0.0:0)
  --stream N          the stream's number (1)
  --rate HZ           frames per second (48000)
  --channels N        samples in a frame (2)
  --bits 16|24        bits of a sample on the wire (24)
  --packet FRAMES     frames in a packet (240)
  --level MS          the latency that receivers hold, in ms (30)
  --signal ramp|tone|silence
                      what the device captures (tone): a ramp that says
                      which frame a sample is, a tone of 440 Hz, or silence
  --cycle FRAMES      frames in a cycle of the device (256)
  --drift PPB         how much faster the device runs, in parts per billion (0)
  --span MS           how long receivers remember samples of the clock (2000)
  --window FRAMES     frames in a window of the clock estimate (2400)
  --seconds S         stop after this long (0: run until stopped)
  --metrics ADDRESS   serve metrics in the Prometheus text format here
  --clock-offset NS, --clock-skew PPB
                      move this process's clock (for tests on one host)
";

/// Runs `unisono send`.
pub(crate) fn run(options: &Options) -> Result<(), Wrong> {
    let receivers = options.addresses("to")?;
    if receivers.is_empty() {
        return Err(Wrong("`--to` must be given".into()));
    }
    let bind: SocketAddr = options.get("bind", SocketAddr::from(([0, 0, 0, 0], 0)))?;
    let rate: u32 = options.get("rate", 48_000)?;
    let channels: u8 = options.get("channels", 2)?;
    let format = match options.get("bits", 24u8)? {
        16 => Format::Signed16,
        24 => Format::Signed24,
        _ => return Err(Wrong("`--bits` is 16 or 24".into())),
    };
    let packet: u16 = options.get("packet", 240)?;
    let level: i64 = options.get("level", 30)?;
    let signal: Signal = options.get("signal", Signal::Tone)?;
    let cycle: usize = options.get("cycle", 256)?;
    let drift: i32 = options.get("drift", 0)?;
    let seconds: i64 = options.get("seconds", 0)?;
    if rate == 0 || channels == 0 || packet == 0 || cycle == 0 {
        return Err(Wrong(
            "the rate, channels, packet and cycle are not zero".into(),
        ));
    }

    let socket = Socket::bind(bind).map_err(|error| Wrong(format!("binding {bind}: {error}")))?;
    let start = clock::raw();
    let device = Device {
        rate,
        channels: usize::from(channels),
        cycle,
        drift,
        start,
        lead: 1_000_000,
        hidden: 0,
    };
    let mut input = Input::new(device, move |position, _, frame: &mut [f32]| {
        signal.fill(position, rate, frame);
    });
    let (mut capture_end, sender_end) = send::link(64, cycle, usize::from(channels));
    let mut network = SenderNetwork::new(
        socket,
        sender_end,
        Settings {
            stream: StreamSettings {
                stream: options.get("stream", 1)?,
                rate,
                channels,
                format,
                span: options.get("span", 2_000)?,
                window: options.get("window", 2_400)?,
                clock: send::clock_identity(),
            },
            packet,
            level: level.saturating_mul(1_000_000),
            timeline: send::first_timeline(),
            receivers,
        },
    );

    let mut metrics = Metrics::new();
    let mut counters = Counters::new(&mut metrics)?;
    if let Some(address) = options.addresses("metrics")?.first() {
        metrics
            .serve(*address)
            .map_err(|error| Wrong(format!("serving metrics at {address}: {error}")))?;
    }

    let stop = Arc::new(AtomicBool::new(false));
    let stopping = Arc::clone(&stop);
    let capture = std::thread::Builder::new()
        .name("unisono-capture".into())
        .stack_size(crate::STACK)
        .spawn(move || {
            while !stopping.load(Ordering::Relaxed) {
                input.run(clock::raw(), &mut capture_end);
                sleep_until(input.due());
            }
            capture_end.dropped()
        })
        .map_err(|error| Wrong(format!("starting the capture thread: {error}")))?;
    // Everything the threads use is made, and they are running.
    if let Err(error) = memory::lock() {
        eprintln!("unisono: memory is not locked: {error}");
    }

    println!("capture start {start} rate {rate} drift {drift} cycle {cycle}");
    let end = start.saturating_add(seconds.saturating_mul(1_000_000_000));
    while seconds == 0 || clock::raw() < end {
        network
            .turn(2)
            .map_err(|error| Wrong(format!("sending: {error}")))?;
        counters.update(network.counts());
        std::thread::sleep(Duration::from_micros(200));
    }
    stop.store(true, Ordering::Relaxed);
    let dropped = capture.join().unwrap_or(0);
    let counts = network.counts();
    println!(
        "sent packets {} answers {} filled {} restarts {} unsent {} dropped-cycles {dropped}",
        counts.packets, counts.answers, counts.filled, counts.restarts, counts.unsent
    );
    Ok(())
}

/// The sender's counters among the metrics.
struct Counters {
    packets: Tally,
    answers: Tally,
    filled: Tally,
    restarts: Tally,
}

impl Counters {
    fn new(metrics: &mut Metrics) -> Result<Counters, Wrong> {
        let named = |error| Wrong(format!("registering metrics: {error:?}"));
        Ok(Counters {
            packets: metrics
                .tally(
                    "unisono_sender_packets_total",
                    "Audio packets made and sent to every receiver.",
                )
                .map_err(named)?,
            answers: metrics
                .tally(
                    "unisono_sender_answers_total",
                    "Reports of receivers answered.",
                )
                .map_err(named)?,
            filled: metrics
                .tally(
                    "unisono_sender_filled_frames_total",
                    "Frames sent as silence for cycles of the capture device that were dropped.",
                )
                .map_err(named)?,
            restarts: metrics
                .tally(
                    "unisono_sender_timeline_restarts_total",
                    "Timelines started after the first.",
                )
                .map_err(named)?,
        })
    }

    fn update(&mut self, counts: SenderCounts) {
        self.packets.update(counts.packets);
        self.answers.update(counts.answers);
        self.filled.update(counts.filled);
        self.restarts.update(counts.restarts);
    }
}
