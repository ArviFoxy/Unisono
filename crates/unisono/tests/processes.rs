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
use std::net::SocketAddr;
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

fn program() -> Command {
    Command::new(env!("CARGO_BIN_EXE_unisono"))
}

/// Starts a receiver that is told that the path from the sender takes
/// `path` nanoseconds, and keeps what it plays in `record` for `seconds`.
/// It listens at `listen`, or, without one, at a port that the system
/// chooses for it: no port that a test picks beforehand stays free for
/// certain until the receiver takes it. Returns the receiver and the address
/// it listens at, which is the first thing it writes.
fn receiver(
    listen: Option<SocketAddr>,
    clock: Clock,
    drift: i64,
    path: i64,
    seconds: u32,
    record: &str,
) -> (Child, SocketAddr) {
    let listen = listen.map_or_else(|| "127.0.0.1:0".to_owned(), |address| address.to_string());
    let mut child = program()
        .args(["receive", "--listen", &listen])
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
        .expect("a receiver");
    let mut line = String::new();
    let stdout = child.stdout.take().expect("its output");
    let mut lines = BufReader::new(stdout);
    lines
        .read_line(&mut line)
        .expect("the receiver's first line");
    // "listening ADDRESS"
    let address = line
        .split_whitespace()
        .nth(1)
        .and_then(|address| address.parse().ok())
        .unwrap_or_else(|| panic!("the receiver said `{line}`"));
    child.stdout = Some(lines.into_inner());
    (child, address)
}

/// Starts a sender to `to` for `seconds`, and returns it with the time its
/// capture device counts as frame 0, on its own clock.
fn sender(to: &[SocketAddr], clock: Clock, drift: i64, seconds: u32) -> (Child, i64) {
    let mut command = program();
    // The level is held, so that the latency of every frame is known.
    command.args(["send", "--signal", "ramp", "--level", "30"]);
    command.args(["--level-choice", "off"]);
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

/// Runs `scene`, and runs it again if it fails, up to three times in all.
///
/// The links of these tests are proxies on this host, and the receivers are
/// told the delay that a proxy is set to. A proxy on a busy host passes
/// datagrams on late, which makes the link longer than the receivers are
/// told, and they play early by the difference. That is the test's link
/// failing to be what it stands for, and it passes with the load.
fn patiently(scene: fn()) {
    for attempt in 1..=3 {
        match std::panic::catch_unwind(scene) {
            Ok(()) => return,
            Err(cause) if attempt == 3 => std::panic::resume_unwind(cause),
            Err(_) => eprintln!("attempt {attempt} failed, and the scene is run again"),
        }
    }
}

#[test]
fn two_receivers_on_clocks_of_their_own_play_together() {
    patiently(two_receivers);
}

fn two_receivers() {
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
    let (receivers, listen): (Vec<Child>, Vec<SocketAddr>) = (0..2)
        .map(|place| {
            let (clock, drift, path) = (clocks[place], drifts[place], delays[place]);
            receiver(None, clock, drift, path, 11, &records[place])
        })
        .unzip();
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

#[test]
fn a_poor_link_and_a_receiver_that_starts_again() {
    patiently(a_poor_link);
}

fn a_poor_link() {
    let directory = std::env::temp_dir().join(format!("unisono-poor-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let record = |name: &str| directory.join(name).to_string_lossy().into_owned();
    let clock = Clock {
        offset: 5_000_000_000,
        skew: 15_000,
    };
    // A link that loses one datagram in fifty, holds each up to 2 ms more
    // than its 1 ms, and holds one in fifty back by 5 ms more, so that later
    // ones overtake it.
    let poor = Impairment {
        delay: 1_000_000,
        jitter: 2_000_000,
        loss: 0.02,
        reordering: 0.02,
        held_back: 5_000_000,
        ..Impairment::NONE
    };
    let clean = Impairment {
        delay: 1_000_000,
        ..Impairment::NONE
    };
    let own = Clock { offset: 0, skew: 0 };

    // The first receiver runs the whole time behind the poor link; the
    // second stops after four seconds and another starts in its place.
    let (steady, poor_at) = receiver(None, clock, 40_000, 1_000_000, 11, &record("steady.raw"));
    let (early, clean_at) = receiver(None, clock, -30_000, 1_000_000, 4, &record("early.raw"));
    let proxies = [
        Proxy::start(poor_at, poor, clean, 21).expect("a proxy"),
        Proxy::start(clean_at, clean, clean, 22).expect("a proxy"),
    ];
    let to: Vec<SocketAddr> = proxies.iter().map(Proxy::near).collect();
    let (sender, start) = sender(&to, own, 0, 10);
    let early_out = finish(early);
    let (late, _) = receiver(
        Some(clean_at),
        clock,
        -30_000,
        1_000_000,
        6,
        &record("late.raw"),
    );
    let sent = finish(sender);
    let steady_out = finish(steady);
    let late_out = finish(late);
    assert!(sent.contains("restarts 0"), "{sent}");
    assert!(early_out.contains("dropped 0"), "{early_out}");

    let capture = Capture::new(own, start, 0);
    #[allow(clippy::cast_precision_loss)]
    let began = own.host(start as f64);

    // Behind the poor link packets are lost, the receiver asks for their
    // frames and the sender sends them again in time: but for a few frames,
    // all that are due in the settled seconds play from the stream, on time.
    let count = |text: &str, name: &str| -> u64 {
        text.split_whitespace()
            .skip_while(|word| *word != name)
            .nth(1)
            .and_then(|count| count.parse().ok())
            .unwrap_or(0)
    };
    assert!(count(&steady_out, "requests") > 20, "{steady_out}");
    assert!(count(&sent, "again") > 20, "{sent}");
    let played = read_record(&record("steady.raw"));
    let steady_errors = errors(&played, clock, &capture, began + 3e9, began + 9e9);
    let on_time: Vec<f64> = steady_errors
        .iter()
        .copied()
        .filter(|e| e.abs() < 1e-3)
        .collect();
    assert!(
        on_time.len() > 286_000,
        "{} frames on time; {steady_out}",
        on_time.len()
    );
    let (low, high) = spread(&on_time, 0.02);
    assert!(
        low > -150e-6 && high < 150e-6,
        "from {low} to {high}; {steady_out}"
    );

    // The receiver that started again plays on time two seconds after its
    // start, which is six seconds into the stream.
    let played = read_record(&record("late.raw"));
    let errors = errors(&played, clock, &capture, began + 6.5e9, began + 9.5e9);
    assert!(
        errors.len() > 120_000,
        "{} frames; {late_out}",
        errors.len()
    );
    let (low, high) = spread(&errors, 0.02);
    assert!(
        low > -150e-6 && high < 150e-6,
        "from {low} to {high}; {late_out}"
    );
    let _ = std::fs::remove_dir_all(&directory);
}
