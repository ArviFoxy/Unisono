// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The program as processes: a sender and receivers on one host, each with a
//! clock of its own (`--clock-offset`, `--clock-skew`) and a device that runs
//! at a rate of its own (`--drift`), with a proxy in front of each receiver
//! that delays what passes.
//!
//! The sender captures a ramp, whose samples say which frame they are, and
//! each receiver keeps what it played with the times of its device. The test
//! turns every time into the host's clock, and measures for every frame how
//! far its latency is from the level.
//!
//! The receivers are told the delay of their paths. Measured through the
//! proxy, the delay errs high by a few hundred microseconds: the proxy holds
//! a datagram past its time by an amount that varies, and the twenty reports
//! a second of a receiver meet a short hold far more rarely than the two
//! hundred audio packets do. `crates/unisono-runtime/tests/threads.rs` tests
//! the measurement.

use std::io::{BufRead, BufReader, Read};
use std::net::{SocketAddr, UdpSocket};
use std::process::{Child, Command, Stdio};

use unisono_runtime::proxy::{Impairment, Proxy};
use unisono_runtime::software::Device;

/// The level that the sender announces: 30 ms.
const LEVEL: i64 = 30_000_000;

/// A clock of a process: it reads `t + offset + t * skew / 10^9` when the
/// host's raw clock reads `t`.
#[derive(Clone, Copy)]
struct Clock {
    offset: i64,
    skew: i64,
}

impl Clock {
    /// The host's time when this clock reads `time`.
    fn host(self, time: f64) -> f64 {
        // Offsets and skews of tests are exact as floats.
        #[allow(clippy::cast_precision_loss)]
        let (offset, skew) = (self.offset as f64, self.skew as f64);
        (time - offset) / (1.0 + skew * 1e-9)
    }

    fn arguments(self) -> [String; 4] {
        [
            "--clock-offset".into(),
            self.offset.to_string(),
            "--clock-skew".into(),
            self.skew.to_string(),
        ]
    }
}

/// A free port on the loopback interface.
fn free() -> SocketAddr {
    let socket = UdpSocket::bind("127.0.0.1:0").expect("a socket");
    socket.local_addr().expect("its address")
}

fn program() -> Command {
    Command::new(env!("CARGO_BIN_EXE_unisono"))
}

/// Starts a receiver that listens at `listen`, is told that the path from
/// the sender takes `path` nanoseconds, and keeps what it plays in `record`
/// for `seconds`.
fn receiver(
    listen: SocketAddr,
    clock: Clock,
    drift: i64,
    path: i64,
    seconds: u32,
    record: &str,
) -> Child {
    program()
        .args(["receive", "--listen", &listen.to_string()])
        .args(["--path", &path.to_string()])
        .args([
            "--drift",
            &drift.to_string(),
            "--seconds",
            &seconds.to_string(),
        ])
        .args(["--record", record])
        .args(clock.arguments())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("a receiver")
}

/// Starts a sender to `to` for `seconds`, and returns it with the time its
/// capture device counts as frame 0, on its own clock.
fn sender(to: &[SocketAddr], clock: Clock, drift: i64, seconds: u32) -> (Child, i64) {
    let mut command = program();
    command.args(["send", "--signal", "ramp", "--level", "30"]);
    for address in to {
        command.args(["--to", &address.to_string()]);
    }
    let mut child = command
        .args([
            "--drift",
            &drift.to_string(),
            "--seconds",
            &seconds.to_string(),
        ])
        .args(clock.arguments())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("a sender");
    let mut line = String::new();
    let stdout = child.stdout.take().expect("its output");
    let mut lines = BufReader::new(stdout);
    lines.read_line(&mut line).expect("the sender's first line");
    // "capture start S rate R drift D cycle C"
    let start = line
        .split_whitespace()
        .nth(2)
        .and_then(|start| start.parse().ok())
        .unwrap_or_else(|| panic!("the sender said `{line}`"));
    child.stdout = Some(lines.into_inner());
    (child, start)
}

/// Waits for a program to end well, and returns what it wrote.
fn finish(mut child: Child) -> String {
    let status = child.wait().expect("the program ends");
    let mut out = String::new();
    if let Some(mut stdout) = child.stdout.take() {
        let _ = stdout.read_to_string(&mut out);
    }
    let mut err = String::new();
    if let Some(mut stderr) = child.stderr.take() {
        let _ = stderr.read_to_string(&mut err);
    }
    assert!(status.success(), "{status}: {out} {err}");
    out
}

/// What a receiver played: its device, and the samples of the first
/// channel.
struct Played {
    device: Device,
    samples: Vec<f32>,
}

fn read_record(path: &str) -> Played {
    let bytes = std::fs::read(path).expect("the record");
    let end = bytes
        .iter()
        .position(|byte| *byte == b'\n')
        .expect("a first line");
    let line = String::from_utf8_lossy(&bytes[..end]);
    let words: Vec<&str> = line.split_whitespace().collect();
    let value = |name: &str| -> i64 {
        let place = words
            .iter()
            .position(|word| *word == name)
            .expect("a field");
        words[place + 1].parse().expect("a number")
    };
    let channels = usize::try_from(value("channels")).expect("channels");
    let device = Device {
        rate: u32::try_from(value("rate")).expect("rate"),
        channels,
        cycle: usize::try_from(value("cycle")).expect("cycle"),
        drift: i32::try_from(value("drift")).expect("drift"),
        start: value("start"),
        lead: value("lead"),
        hidden: 0,
    };
    let samples = bytes[end + 1..]
        .chunks_exact(4 * channels)
        .map(|frame| f32::from_le_bytes([frame[0], frame[1], frame[2], frame[3]]))
        .collect();
    Played { device, samples }
}

/// A sender's capture device, as it reports frames on its own clock.
struct Capture {
    clock: Clock,
    device: Device,
}

impl Capture {
    fn new(clock: Clock, start: i64, drift: i64) -> Capture {
        Capture {
            clock,
            device: Device {
                rate: 48_000,
                channels: 2,
                cycle: 256,
                drift: i32::try_from(drift).expect("a drift"),
                start,
                lead: 1_000_000,
                hidden: 0,
            },
        }
    }

    /// The host's time at which the frame at `position` is due to play: a
    /// level after it was captured, on the sender's clock.
    fn due(&self, position: f64) -> f64 {
        // A position below 2^23 is exact as an integer.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let whole = position.floor() as u64;
        let (before, after) = (self.device.captured(whole), self.device.captured(whole + 1));
        #[allow(clippy::cast_precision_loss)]
        let taken = before as f64 + (after - before) as f64 * position.fract();
        #[allow(clippy::cast_precision_loss)]
        self.clock.host(taken + LEVEL as f64)
    }
}

/// How far from the level the latency of each frame is, in seconds, that a
/// receiver with `clock` played between the host's times `from` and `to`, of
/// what `capture` captured.
fn errors(played: &Played, clock: Clock, capture: &Capture, from: f64, to: f64) -> Vec<f64> {
    let mut errors = Vec::new();
    for (count, sample) in (0u64..).zip(&played.samples) {
        #[allow(clippy::cast_precision_loss)]
        let left = clock.host(played.device.played(count) as f64);
        if left < from || left > to || *sample <= 0.0 {
            continue;
        }
        let position = f64::from(*sample) * 8_388_608.0 - 1.0;
        errors.push((left - capture.due(position)) * 1e-9);
    }
    errors.sort_by(f64::total_cmp);
    errors
}

/// The share `share` of `errors` from either end.
fn spread(errors: &[f64], share: f64) -> (f64, f64) {
    // A count of frames is exact as a float.
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss
    )]
    let place = |at: f64| ((errors.len() - 1) as f64 * at) as usize;
    (errors[place(share)], errors[place(1.0 - share)])
}

#[test]
fn two_receivers_on_clocks_of_their_own_play_together() {
    let directory = std::env::temp_dir().join(format!("unisono-processes-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let records = [
        directory.join("first.raw").to_string_lossy().into_owned(),
        directory.join("second.raw").to_string_lossy().into_owned(),
    ];
    // Two hosts an hour and a second apart, 30 and -20 parts per million
    // fast against the sender's, with devices 80 and -60 fast against
    // their hosts.
    let clocks = [
        Clock {
            offset: 3_600_000_000_000,
            skew: 30_000,
        },
        Clock {
            offset: -1_000_000_000,
            skew: -20_000,
        },
    ];
    let drifts = [80_000, -60_000];
    let delays = [1_000_000, 3_000_000];
    let listen = [free(), free()];
    let proxies: Vec<Proxy> = listen
        .iter()
        .zip(delays)
        .map(|(address, delay)| {
            let path = Impairment {
                delay,
                ..Impairment::NONE
            };
            Proxy::start(*address, path, path, 9).expect("a proxy")
        })
        .collect();
    let receivers: Vec<Child> = (0..2)
        .map(|place| {
            let (clock, drift, path) = (clocks[place], drifts[place], delays[place]);
            receiver(listen[place], clock, drift, path, 11, &records[place])
        })
        .collect();
    let to: Vec<SocketAddr> = proxies.iter().map(Proxy::near).collect();

    // The sender runs for five seconds, and another for five more: a sender
    // that started again, with a new timeline and its capture device's count
    // from zero.
    let own = Clock {
        offset: 77_000_000,
        skew: 0,
    };
    let (first, first_start) = sender(&to, own, 50_000, 5);
    let first_out = finish(first);
    let (second, second_start) = sender(&to, own, 50_000, 5);
    let second_out = finish(second);
    let outs: Vec<String> = receivers.into_iter().map(finish).collect();
    assert!(first_out.contains("restarts 0"), "{first_out}");
    assert!(second_out.contains("restarts 0"), "{second_out}");

    let first_capture = Capture::new(own, first_start, 50_000);
    let second_capture = Capture::new(own, second_start, 50_000);
    // The host's times at which the two senders' first frames were taken.
    #[allow(clippy::cast_precision_loss)]
    let (first_began, second_began) = (own.host(first_start as f64), own.host(second_start as f64));
    for place in 0..2 {
        let played = read_record(&records[place]);
        // The last two seconds of each sender, once the receiver has
        // measured its path and settled.
        for (capture, began) in [
            (&first_capture, first_began),
            (&second_capture, second_began),
        ] {
            let errors = errors(&played, clocks[place], capture, began + 3e9, began + 5e9);
            assert!(
                errors.len() > 80_000,
                "receiver {place}: {} frames, {}",
                errors.len(),
                outs[place]
            );
            let (low, high) = spread(&errors, 0.02);
            assert!(
                low > -150e-6 && high < 150e-6,
                "receiver {place}: from {low} to {high}; {}",
                outs[place]
            );
        }
    }
    let _ = std::fs::remove_dir_all(&directory);
}
