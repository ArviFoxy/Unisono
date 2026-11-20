// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Prints inputs and results of the core's functions.
//!
//! The proofs are about the Lean translation of the core, so they say
//! something about the Rust only if the translation computes what the Rust
//! computes. `lean/TranslationCheck.lean` reads the lines printed here,
//! evaluates the translated function on the same inputs and compares.
//!
//! Each line is the name of a function, its arguments, `->` and its results.

use std::io::{self, BufWriter, Write};

use unisono_core::{device, fixed, packet, player, presence, receiver, relation, sender, timing};

/// Values at which integer arithmetic tends to go wrong: zero, the extremes,
/// and both sides of the powers of two that the core uses as scales.
fn boundary_values() -> Vec<i64> {
    let mut values = vec![0, 1, -1, i64::MAX, i64::MIN, i64::MAX - 1, i64::MIN + 1];
    for bit in [1, 31, 32, 47, 48, 62] {
        let power = 1i64 << bit;
        values.extend([power - 1, power, power + 1, -power - 1, -power, -power + 1]);
    }
    values
}

/// A sequence of numbers that is the same on every run (the `SplitMix64`
/// generator), so that a difference found once can be found again.
struct Sequence(u64);

impl Sequence {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A signed number whose magnitude is spread over all bit lengths.
    fn signed(&mut self) -> i64 {
        let bits = self.next() % 65;
        let value = if bits == 0 {
            0
        } else {
            self.next() >> (64 - bits)
        };
        value.cast_signed()
    }
}

fn saturate_cases(out: &mut impl Write) -> io::Result<()> {
    let limits = [i128::from(i64::MAX), i128::from(i64::MIN)];
    let mut inputs = vec![0, i128::MAX, i128::MIN];
    for limit in limits {
        inputs.extend([limit - 1, limit, limit + 1]);
    }
    inputs.extend(boundary_values().into_iter().map(i128::from));
    for x in inputs {
        writeln!(out, "saturate {x} -> {}", fixed::saturate(x))?;
    }
    Ok(())
}

fn mul_shift_cases(out: &mut impl Write) -> io::Result<()> {
    let shifts = [0, 1, 2, 31, 32, 47, 48, 63, 64, 65, u32::MAX];
    let values = boundary_values();
    for &a in &values {
        for &b in &values {
            for shift in shifts {
                writeln!(
                    out,
                    "mul_shift {a} {b} {shift} -> {}",
                    fixed::mul_shift(a, b, shift)
                )?;
            }
        }
    }
    let mut sequence = Sequence(1);
    for _ in 0..2000 {
        let (a, b) = (sequence.signed(), sequence.signed());
        let shift = u32::try_from(sequence.next() % 66).unwrap_or(0);
        writeln!(
            out,
            "mul_shift {a} {b} {shift} -> {}",
            fixed::mul_shift(a, b, shift)
        )?;
    }
    Ok(())
}

fn div_floor_cases(out: &mut impl Write) -> io::Result<()> {
    let divisors = [1, 2, 3, 7, 1 << 32, i64::MAX, 0, -1, i64::MIN];
    let mut dividends = vec![i128::MAX, i128::MIN, i128::MIN + 1];
    dividends.extend(boundary_values().into_iter().map(i128::from));
    for &a in &dividends {
        for b in divisors {
            writeln!(out, "div_floor {a} {b} -> {}", fixed::div_floor(a, b))?;
        }
    }
    let wide_divisors = [
        1i128,
        2,
        3,
        7,
        1 << 64,
        1 << 100,
        i128::MAX,
        0,
        -1,
        i128::MIN,
    ];
    for &a in &dividends {
        for b in wide_divisors {
            writeln!(
                out,
                "div_floor_wide {a} {b} -> {}",
                fixed::div_floor_wide(a, b)
            )?;
        }
    }
    Ok(())
}

/// Runs of packets through the estimator of a clock relation. Times mostly
/// increase and sometimes stand still or go back; values scatter above a
/// line; windows hold one to four packets. A line of output is the span, the
/// limit of the slope, the number of packets, each packet's window, time and value, and after `->`
/// whether there is a line, the line and the number of samples kept.
fn relation_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(2);
    for case in 0..400u64 {
        let span = [900, 60_000, i64::MAX][usize::try_from(case % 3).unwrap_or(0)];
        let packets = 1 + sequence.next() % 48;
        let limit = [5, 200_000, i64::MAX][usize::try_from(case / 3 % 3).unwrap_or(0)];
        let mut estimator = relation::Estimator::<8>::new(span, limit);
        write!(out, "relation {span} {limit} {packets}")?;
        let (mut window, mut time) = (sequence.next() % 5, sequence.signed() % 1_000_000);
        let slope = sequence.signed() % 2000;
        for _ in 0..packets {
            if sequence.next().is_multiple_of(3) {
                window += 1;
            }
            time += match sequence.next() % 40 {
                0 => -300,
                1 => 0,
                _ => 1 + (sequence.signed() % 500).abs(),
            };
            let delay = if sequence.next().is_multiple_of(2) {
                0
            } else {
                (sequence.signed() % 4000).abs()
            };
            let value = 12_345 + time / 1000 * slope + delay;
            estimator.observe(window, relation::Sample { time, value });
            write!(out, " {window} {time} {value}")?;
        }
        estimator.end_window();
        match estimator.line() {
            Some(line) => {
                writeln!(
                    out,
                    " -> 1 {} {} {} {} {}",
                    line.time,
                    line.value,
                    line.rise,
                    line.run,
                    estimator.kept()
                )?;
            }
            None => writeln!(out, " -> 0 0 0 0 0 {}", estimator.kept())?,
        }
    }
    Ok(())
}

/// The fields of a header as numbers, in the order of the layout.
fn fields(header: &packet::Audio) -> [i128; 18] {
    [
        i128::from(header.stream),
        i128::from(header.timeline),
        i128::from(header.index),
        i128::from(header.capture),
        i128::from(header.rate),
        i128::from(header.frames),
        i128::from(header.channels),
        match header.format {
            packet::Format::Signed16 => 1,
            packet::Format::Signed24 => 2,
        },
        i128::from(header.level),
        i128::from(header.level_slope),
        i128::from(header.span),
        i128::from(header.window),
        i128::from(header.flags),
        i128::from(header.protection),
        i128::from(header.stamped_index),
        i128::from(header.stamped_departure),
        i128::from(header.drift),
        i128::from(header.clock),
    ]
}

/// What parsing gives, as numbers: 0 and the fields, or the number of the
/// reason for rejection, its detail, and zeros.
fn parsed(bytes: &[u8]) -> [i128; 19] {
    let mut numbers = [0i128; 19];
    match packet::parse_audio(bytes) {
        Ok(header) => numbers[1..].copy_from_slice(&fields(&header)),
        Err(reason) => {
            let [code, detail] = rejection(reason);
            numbers[0] = code;
            numbers[1] = detail;
        }
    }
    numbers
}

/// What `packet::kind` gives: `[0, kind]` or `[code, detail]`.
fn kind_numbers(bytes: &[u8]) -> [i128; 2] {
    match packet::kind(bytes) {
        Ok(found) => [0, i128::from(found)],
        Err(reason) => rejection(reason),
    }
}

fn join(numbers: &[i128]) -> String {
    numbers
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

fn bytes_of(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

/// Draws a random audio header; when `valid` is true, its semantic fields pass
/// `parse_audio`'s checks.
#[allow(clippy::cast_possible_truncation)]
fn random_audio(sequence: &mut Sequence, valid: bool) -> packet::Audio {
    packet::Audio {
        stream: sequence.next() as u16,
        timeline: sequence.next(),
        index: sequence.next(),
        capture: sequence.signed(),
        rate: if valid {
            1 + (sequence.next() as u32 % 192_000)
        } else {
            sequence.next() as u32
        },
        frames: (sequence.next() % 4) as u16,
        channels: if valid {
            1 + (sequence.next() % 4) as u8
        } else {
            (sequence.next() % 4) as u8
        },
        format: if sequence.next().is_multiple_of(2) {
            packet::Format::Signed16
        } else {
            packet::Format::Signed24
        },
        level: sequence.signed(),
        level_slope: if valid {
            (sequence.signed() % 999_999_999) as i32
        } else {
            sequence.signed() as i32
        },
        span: sequence.next() as u32,
        window: sequence.next() as u32,
        flags: if valid {
            (sequence.next() % 2) as u16
        } else {
            sequence.next() as u16
        },
        protection: if valid { 0 } else { sequence.next() as u16 },
        stamped_index: sequence.next(),
        stamped_departure: sequence.signed(),
        drift: if valid {
            (sequence.signed() % 999_999_999) as i32
        } else {
            sequence.signed() as i32
        },
        clock: sequence.next() as u32,
    }
}

/// Headers drawn at random, written and read back, and the same packets with
/// one byte changed, one byte more, and one byte less.
fn packet_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(3);
    for round in 0..150 {
        let header = random_audio(&mut sequence, round % 2 == 0);
        let mut buffer = [0u8; 256];
        let Some(length) = packet::write_audio(&header, &mut buffer) else {
            continue;
        };
        let good = &buffer[..length];
        writeln!(
            out,
            "write_audio {} -> {length} {}",
            join(&fields(&header)),
            bytes_of(&buffer[..packet::HEADER])
        )?;
        writeln!(
            out,
            "parse_audio {} -> {}",
            bytes_of(good),
            join(&parsed(good))
        )?;
        writeln!(
            out,
            "packet_kind {} -> {}",
            bytes_of(good),
            join(&kind_numbers(good))
        )?;
        let mut changed = good.to_vec();
        let place = usize::try_from(sequence.next() % packet::HEADER as u64).unwrap_or(0);
        changed[place] ^= 1 << (sequence.next() % 8);
        writeln!(
            out,
            "parse_audio {} -> {}",
            bytes_of(&changed),
            join(&parsed(&changed))
        )?;
        writeln!(
            out,
            "packet_kind {} -> {}",
            bytes_of(&changed),
            join(&kind_numbers(&changed))
        )?;
        let mut longer = good.to_vec();
        longer.push(0);
        writeln!(
            out,
            "parse_audio {} -> {}",
            bytes_of(&longer),
            join(&parsed(&longer))
        )?;
        let shorter = &good[..length - 1];
        writeln!(
            out,
            "parse_audio {} -> {}",
            bytes_of(shorter),
            join(&parsed(shorter))
        )?;
    }
    Ok(())
}

/// Runs of operations on a stretch of 192 indices. Each operation is three
/// numbers: 0, a first index and a number of frames, to mark; 1, an index
/// and 0, to advance; 2, an index and 0, to ask whether it is held; 3, an
/// index and a limit, to count the frames held from it on. The results follow
/// `->`: four counts for a mark, the start of the stretch for an advance, 0
/// or 1 for a question, the count for a run.
fn presence_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(4);
    for _ in 0..200 {
        let mut presence = presence::Presence::<3>::new();
        let operations = 1 + sequence.next() % 30;
        let mut results: Vec<i128> = Vec::new();
        write!(out, "presence {operations}")?;
        let mut near = sequence.next() % 500;
        for _ in 0..operations {
            let index = (near + sequence.next() % 260).saturating_sub(40);
            let amount = u32::try_from(sequence.next() % 50).unwrap_or(0);
            match sequence.next() % 4 {
                0 => {
                    let marked = presence.mark(index, amount);
                    write!(out, " 0 {index} {amount}")?;
                    results.extend(
                        [marked.stored, marked.duplicate, marked.late, marked.early]
                            .map(i128::from),
                    );
                }
                1 => {
                    presence.advance(index);
                    near = near.max(index);
                    write!(out, " 1 {index} 0")?;
                    results.push(i128::from(presence.base()));
                }
                2 => {
                    write!(out, " 2 {index} 0")?;
                    results.push(i128::from(presence.held(index)));
                }
                _ => {
                    write!(out, " 3 {index} {amount}")?;
                    results.push(i128::from(presence.run(index, amount)));
                }
            }
        }
        writeln!(out, " -> {}", join(&results))?;
    }
    Ok(())
}

/// A plan as numbers: its frames, the frame and fraction of its start, its
/// step and whether it jumped.
fn plan_numbers(plan: &player::Plan) -> [i128; 5] {
    [
        i128::from(plan.frames),
        i128::from(plan.start.frame),
        i128::from(plan.start.fraction),
        i128::from(plan.step),
        i128::from(plan.jumped),
    ]
}

/// The header that the receiver cases use: the numbers that vary, and the
/// rest fixed.
fn stream_header(
    timeline: u64,
    index: u64,
    frames: u16,
    flags: u16,
    stamped_index: u64,
    stamped_departure: i64,
) -> packet::Audio {
    packet::Audio {
        stream: 1,
        timeline,
        index,
        // A frame of 48,000 a second lasts 20,833 nanoseconds.
        capture: i64::try_from(index).unwrap_or(0).saturating_mul(20_833),
        drift: 0,
        rate: 48_000,
        frames,
        channels: 2,
        format: packet::Format::Signed16,
        level: 0,
        level_slope: 0,
        span: 20,
        window: 50,
        flags,
        protection: 0,
        stamped_index,
        stamped_departure,
        clock: 1,
    }
}

/// Runs of operations on a receiver that holds 128 frames, remembers four
/// samples of the sender's clock and keeps two arrivals. Each operation is
/// eight numbers. 0, a timeline, an index, a number of frames, flags, a
/// stamped index, a stamped departure and an arrival time: a packet, whose
/// results are whether it was ignored, whether its timeline was taken up,
/// and the four counts of its frames. 1 and a limit: a run of frames is
/// taken, and the results are its first index, its length and whether it is
/// held. 2 and an index: a skip, whose result is the number of frames
/// skipped. 3, a time and a number of frames: a cycle of the device, whose
/// results are the plan's number of frames, the frame and the fraction of
/// its start, its step and whether it jumped. 4, a receiver and a delay: a
/// report is made, has left now, and is answered for that receiver as
/// having arrived after the delay; the results are the report's number, or
/// -1 when none was made, and the delay of the path afterwards. After every
/// operation the followed timeline, or -1, and the playhead follow. At the end come the line of the clock estimate, or
/// zeros, and the index of the schedule, or -1.
// One arm for each kind of operation; apart they would share most of their
// arguments.
#[allow(clippy::too_many_lines)]
fn receiver_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(5);
    for _ in 0..200 {
        let silence = 1_000 + sequence.next() % 5_000;
        let regulation = player::Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: 30,
        };
        let mut receiver = receiver::Receiver::<2, 4, 2>::new(receiver::Settings {
            identity: 9,
            silence: i64::try_from(silence).unwrap_or(0),
            limit: 200_000,
            regulation,
        });
        let operations = 1 + sequence.next() % 40;
        let mut results: Vec<i128> = Vec::new();
        write!(out, "receiver {silence} {operations}")?;
        let mut now = 0i64;
        let mut near = sequence.next() % 1_000;
        // Most packets are of one timeline and carry the departure of one of
        // the two packets before, so that the estimate of the clock gets
        // samples.
        let mut timeline = 2u64;
        let mut recent = [0u64; 2];
        for _ in 0..operations {
            match sequence.next() % 7 {
                3 => {
                    let to = 9 - sequence.next() % 8 / 7;
                    let delay = i64::try_from(sequence.next() % 500).unwrap_or(0);
                    write!(out, " 4 {to} {delay} {now} 0 0 0 0")?;
                    let number = receiver.report(1).map(|report| {
                        receiver.reported(report.sequence, now);
                        receiver.echo(&packet::Echo {
                            stream: 1,
                            receiver: to,
                            sequence: report.sequence,
                            arrival: now + delay,
                        });
                        report.sequence
                    });
                    results.push(number.map_or(-1, i128::from));
                    results.push(i128::from(receiver.delay()));
                }
                2 => {
                    let frames = u32::try_from(sequence.next() % 40).unwrap_or(0);
                    let time = now + i64::try_from(sequence.next() % 400_000).unwrap_or(0);
                    let plan = receiver.cycle(time, i64::from(frames) * 20_833, frames);
                    write!(out, " 3 {time} {frames} 0 0 0 0 0")?;
                    results.extend(plan_numbers(&plan));
                }
                0 => {
                    let limit = u32::try_from(sequence.next() % 40).unwrap_or(0);
                    let segment = receiver.take(limit);
                    write!(out, " 1 {limit} 0 0 0 0 0 0")?;
                    results.extend([
                        i128::from(segment.first),
                        i128::from(segment.frames),
                        i128::from(segment.held),
                    ]);
                }
                1 => {
                    let to = (near + sequence.next() % 60).saturating_sub(20);
                    write!(out, " 2 {to} 0 0 0 0 0 0")?;
                    results.push(i128::from(receiver.skip(to)));
                }
                _ => {
                    now += i64::try_from(sequence.next() % 2_500).unwrap_or(0) - 100;
                    if sequence.next().is_multiple_of(12) {
                        timeline = 1 + sequence.next() % 3;
                    }
                    let index = (near + sequence.next() % 200).saturating_sub(40) / 10 * 10;
                    let frames = u16::try_from(sequence.next() % 25).unwrap_or(0);
                    let flags = u16::try_from(sequence.next() % 4).unwrap_or(0);
                    let stamped_index = if sequence.next().is_multiple_of(2) {
                        recent[0]
                    } else {
                        recent[1]
                    };
                    recent = [recent[1], index];
                    let stamped_departure = now - i64::try_from(sequence.next() % 300).unwrap_or(0);
                    let header = stream_header(
                        timeline,
                        index,
                        frames,
                        flags,
                        stamped_index,
                        stamped_departure,
                    );
                    let heard = receiver.packet(&header, now);
                    write!(
                        out,
                        " 0 {timeline} {index} {frames} {flags} {stamped_index} {stamped_departure} {now}"
                    )?;
                    results.extend([
                        i128::from(heard.ignored),
                        i128::from(heard.adopted),
                        i128::from(heard.restarted),
                        i128::from(heard.marked.stored),
                        i128::from(heard.marked.duplicate),
                        i128::from(heard.marked.late),
                        i128::from(heard.marked.early),
                    ]);
                }
            }
            near = near.max(receiver.playhead());
            results.push(receiver.timeline().map_or(-1, i128::from));
            results.push(i128::from(receiver.playhead()));
        }
        let line = receiver
            .clock()
            .map_or([0; 4], |line| [line.time, line.value, line.rise, line.run]);
        results.extend(line.map(i128::from));
        results.push(
            receiver
                .schedule()
                .map_or(-1, |schedule| i128::from(schedule.index)),
        );
        writeln!(out, " -> {}", join(&results))?;
    }
    Ok(())
}

/// Runs of operations on a sender. Each operation is four numbers. 0, a
/// number of frames, a capture time and a drift: the header of the next
/// packet, of which the index, the flags, the stamped index, the stamped
/// departure, the capture time, the drift, the level and the level slope are
/// the results. 1, a timeline, an index and a departure: a departure is taken
/// in. 2 and a timeline: a restart. 3, a level and a slope: sets the level
/// ramp. 4, a stream, a sequence and an arrival: answers a report, giving 1
/// and the echo fields, or 0 and zeros. After every operation the timeline,
/// the index of the next frame and the current level follow.
fn sender_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(6);
    for _ in 0..200 {
        let settings = sender::Settings {
            stream: 1,
            rate: 48_000,
            channels: 2,
            format: packet::Format::Signed16,
            span: 20,
            window: 50,
            clock: 1,
        };
        let first = sequence.next() % 4;
        let mut sender = sender::Sender::new(settings, first, 0);
        let operations = 1 + sequence.next() % 30;
        let mut results: Vec<i128> = Vec::new();
        write!(out, "sender {first} {operations}")?;
        for _ in 0..operations {
            match sequence.next() % 8 {
                0 => {
                    let timeline = sequence.next() % 8;
                    write!(out, " 2 {timeline} 0 0")?;
                    sender.restart(timeline);
                }
                1 | 2 => {
                    let timeline = sender.timeline().saturating_sub(sequence.next() % 2);
                    let index = sequence.next() % (sender.next() + 30);
                    let departure = sequence.signed();
                    write!(out, " 1 {timeline} {index} {departure}")?;
                    sender.departed(timeline, index, departure);
                }
                3 => {
                    let level = sequence.signed() % 1_000_000_000_000;
                    // The cast keeps the low bits of a random number.
                    #[allow(clippy::cast_possible_truncation)]
                    let slope = (sequence.signed() % 2_000_000_000) as i32;
                    write!(out, " 3 {level} {slope} 0")?;
                    sender.level(level, slope);
                }
                4 => {
                    let stream = u16::try_from(1 + sequence.next() % 2).unwrap_or(1);
                    let number = sequence.next();
                    let arrival = sequence.signed();
                    let report = packet::Report {
                        stream,
                        timeline: sender.timeline(),
                        receiver: 42,
                        sequence: number,
                    };
                    write!(out, " 4 {stream} {number} {arrival}")?;
                    match sender.answer(&report, arrival) {
                        Some(echo) => results.extend([
                            1,
                            i128::from(echo.stream),
                            i128::from(echo.receiver),
                            i128::from(echo.sequence),
                            i128::from(echo.arrival),
                        ]),
                        None => results.extend([0, 0, 0, 0, 0]),
                    }
                }
                _ => {
                    let frames = u16::try_from(sequence.next() % 300).unwrap_or(0);
                    let capture = sequence.signed();
                    // The cast keeps the low bits of a random number.
                    #[allow(clippy::cast_possible_truncation)]
                    let drift = sequence.signed() as i32;
                    write!(out, " 0 {frames} {capture} {drift}")?;
                    let header = sender.packet(frames, capture, drift);
                    results.extend([
                        i128::from(header.index),
                        i128::from(header.flags),
                        i128::from(header.stamped_index),
                        i128::from(header.stamped_departure),
                        i128::from(header.capture),
                        i128::from(header.drift),
                        i128::from(header.level),
                        i128::from(header.level_slope),
                    ]);
                }
            }
            results.push(i128::from(sender.timeline()));
            results.push(i128::from(sender.next()));
            results.push(i128::from(sender.current_level()));
        }
        writeln!(out, " -> {}", join(&results))?;
    }
    Ok(())
}

/// Readings of clocks turned into positions of a stream, and positions moved
/// and compared, at boundary values and at random ones.
fn timing_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(7);
    let boundaries = boundary_values();
    let pick = |sequence: &mut Sequence| {
        if sequence.next().is_multiple_of(4) {
            let place = usize::try_from(sequence.next()).unwrap_or(0) % boundaries.len();
            boundaries[place]
        } else {
            sequence.signed()
        }
    };
    for _ in 0..600 {
        let line = relation::Line {
            time: pick(&mut sequence),
            value: pick(&mut sequence),
            rise: sequence.signed() % 1_000_000,
            run: 1 + i64::try_from(sequence.next() % 20_000_000_000).unwrap_or(0),
        };
        let path = sequence.signed() % 10_000_000;
        let time = pick(&mut sequence);
        writeln!(
            out,
            "sender_time {} {} {} {} {path} {time} -> {}",
            line.time,
            line.value,
            line.rise,
            line.run,
            timing::sender_time(&line, path, time)
        )?;
        // The casts keep the low bits of random numbers.
        #[allow(clippy::cast_possible_truncation)]
        let schedule = timing::Schedule {
            index: sequence.next() >> (sequence.next() % 64),
            capture: pick(&mut sequence),
            rate: [44_100, 48_000, 96_000, 0, u32::MAX]
                [usize::try_from(sequence.next() % 5).unwrap_or(0)],
            drift: (sequence.signed() % 2_000_000_000) as i32,
            level: sequence.signed() % 1_000_000_000_000,
            level_slope: (sequence.signed() % 2_000_000_000) as i32,
        };
        let at = pick(&mut sequence);
        let position = timing::due(&schedule, at);
        writeln!(
            out,
            "due {} {} {} {} {} {} {at} -> {}",
            schedule.index,
            schedule.capture,
            schedule.rate,
            schedule.drift,
            schedule.level,
            schedule.level_slope,
            match position {
                Some(position) => format!("1 {} {}", position.frame, position.fraction),
                None => "0 0 0".to_string(),
            }
        )?;
        let from = timing::Position {
            frame: sequence.next() >> (sequence.next() % 64),
            fraction: sequence.next(),
        };
        let to = timing::Position {
            frame: sequence.next() >> (sequence.next() % 64),
            fraction: sequence.next(),
        };
        writeln!(
            out,
            "distance {} {} {} {} -> {}",
            from.frame,
            from.fraction,
            to.frame,
            to.fraction,
            timing::distance(from, to)
        )?;
        #[allow(clippy::cast_possible_truncation)]
        let frames = sequence.next() as u32 >> (sequence.next() % 32);
        let step = pick(&mut sequence);
        let moved = timing::advance(from, frames, step);
        writeln!(
            out,
            "advance {} {} {frames} {step} -> {} {}",
            from.frame, from.fraction, moved.frame, moved.fraction
        )?;
    }
    Ok(())
}

/// Runs of cycles through a regulator. Each cycle is six numbers: the frame
/// and fraction of the position due at its start, the same for its end, the
/// number of frames and the duration. The results of each are the plan's
/// number of frames, the frame and fraction of its start, its step and
/// whether it jumped.
fn player_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(8);
    for _ in 0..200 {
        // The casts keep the low bits of random numbers.
        #[allow(clippy::cast_possible_truncation)]
        let regulation = player::Regulation {
            gain: sequence.next() as u32 >> (sequence.next() % 32),
            limit: sequence.next() as u32 >> (sequence.next() % 32),
            jump: sequence.next() as u32 >> (8 + sequence.next() % 24),
        };
        let mut player = player::Player::new(regulation);
        let cycles = 1 + sequence.next() % 30;
        write!(
            out,
            "player {} {} {} {cycles}",
            regulation.gain, regulation.limit, regulation.jump
        )?;
        let mut results: Vec<i128> = Vec::new();
        let mut now = timing::Position {
            frame: sequence.next() % 1_000_000,
            fraction: sequence.next(),
        };
        for _ in 0..cycles {
            let frames = u32::try_from(sequence.next() % 600).unwrap_or(0);
            // Mostly a schedule near one frame for a frame, at times one that
            // is far off or runs backwards.
            let step = match sequence.next() % 8 {
                0 => sequence.signed(),
                1 => i64::MIN,
                _ => sequence.signed() % (1 << 52),
            };
            let then = timing::advance(now, frames, step);
            let duration = i64::from(frames) * 20_833 + sequence.signed() % 1_000;
            let plan = player.cycle(now, then, frames, duration);
            write!(
                out,
                " {} {} {} {} {frames} {duration}",
                now.frame, now.fraction, then.frame, then.fraction
            )?;
            results.extend(plan_numbers(&plan));
            // At times the schedule moves away from where the regulator is.
            now = match sequence.next() % 6 {
                0 => timing::advance(then, u32::try_from(sequence.next() % 400).unwrap_or(0), 0),
                1 => timing::Position {
                    frame: then.frame.saturating_sub(sequence.next() % 400),
                    fraction: then.fraction,
                },
                _ => then,
            };
        }
        writeln!(out, " -> {}", join(&results))?;
    }
    Ok(())
}

/// Reports and answers to them, written and read back, and the same packets
/// with one byte changed and with one byte less.
fn report_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(9);
    for _ in 0..150 {
        // The casts keep the low bits of random numbers.
        #[allow(clippy::cast_possible_truncation)]
        let report = packet::Report {
            stream: sequence.next() as u16,
            timeline: sequence.next(),
            receiver: sequence.next(),
            sequence: sequence.next(),
        };
        let length = usize::try_from(sequence.next() % 80).unwrap_or(0);
        let mut buffer = [0xa5u8; 96];
        let written = packet::write_report(&report, &mut buffer, length);
        writeln!(
            out,
            "write_report {} {} {} {} {length} -> {} {}",
            report.stream,
            report.timeline,
            report.receiver,
            report.sequence,
            written.map_or(-1, |n| i128::try_from(n).unwrap_or(-1)),
            bytes_of(&buffer)
        )?;
        #[allow(clippy::cast_possible_truncation)]
        let echo = packet::Echo {
            stream: sequence.next() as u16,
            receiver: sequence.next(),
            sequence: sequence.next(),
            arrival: sequence.signed(),
        };
        let mut answer = [0u8; 40];
        let size = packet::write_echo(&echo, &mut answer).unwrap_or(0);
        writeln!(
            out,
            "write_echo {} {} {} {} -> {size} {}",
            echo.stream,
            echo.receiver,
            echo.sequence,
            echo.arrival,
            bytes_of(&answer)
        )?;
        let used = written.unwrap_or(0);
        let mut changed = buffer[..used].to_vec();
        let place = usize::try_from(sequence.next() % 32).unwrap_or(0);
        if let Some(byte) = changed.get_mut(place) {
            *byte ^= 1 << (sequence.next() % 8);
        }
        let mut changed_answer = answer[..size].to_vec();
        if let Some(byte) = changed_answer.get_mut(place) {
            *byte ^= 1 << (sequence.next() % 8);
        }
        for bytes in [
            &buffer[..used],
            &changed[..],
            &buffer[..used.saturating_sub(1).min(31)],
            &answer[..size],
            &changed_answer[..],
            &answer[..=size],
        ] {
            writeln!(
                out,
                "parse_report {} -> {}",
                bytes_of(bytes),
                join(&report_numbers(bytes))
            )?;
            writeln!(
                out,
                "parse_echo {} -> {}",
                bytes_of(bytes),
                join(&echo_numbers(bytes))
            )?;
        }
    }
    Ok(())
}

/// A reason for rejection as two numbers: which reason, and its detail.
fn rejection(reason: packet::Rejected) -> [i128; 2] {
    match reason {
        packet::Rejected::TooShort => [1, 0],
        packet::Rejected::NotUnisono => [2, 0],
        packet::Rejected::Version(version) => [3, i128::from(version)],
        packet::Rejected::Kind(kind) => [4, i128::from(kind)],
        packet::Rejected::Format(format) => [5, i128::from(format)],
        packet::Rejected::Length => [6, 0],
        packet::Rejected::Rate => [7, 0],
        packet::Rejected::Channels => [8, 0],
        packet::Rejected::Flags(flags) => [9, i128::from(flags)],
        packet::Rejected::Protection(protection) => [10, i128::from(protection)],
        packet::Rejected::Pace => [11, 0],
    }
}

/// What reading a report gives, as numbers: 0 and its fields, or the reason
/// for rejection and zeros.
fn report_numbers(bytes: &[u8]) -> [i128; 5] {
    match packet::parse_report(bytes) {
        Ok(report) => [
            0,
            i128::from(report.stream),
            i128::from(report.timeline),
            i128::from(report.receiver),
            i128::from(report.sequence),
        ],
        Err(reason) => {
            let [code, detail] = rejection(reason);
            [code, detail, 0, 0, 0]
        }
    }
}

/// What reading an answer to a report gives, as numbers: 0 and its fields,
/// or the reason for rejection and zeros.
fn echo_numbers(bytes: &[u8]) -> [i128; 5] {
    match packet::parse_echo(bytes) {
        Ok(echo) => [
            0,
            i128::from(echo.stream),
            i128::from(echo.receiver),
            i128::from(echo.sequence),
            i128::from(echo.arrival),
        ],
        Err(reason) => {
            let [code, detail] = rejection(reason);
            [code, detail, 0, 0, 0]
        }
    }
}

/// Runs of reports through the line of a device with room for four. Each
/// report is a position and a time. After every report the line is asked
/// for the time of a position; the results are 1 and that time, or 0 and 0.
fn device_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(10);
    for _ in 0..300 {
        let rate =
            [48_000u32, 44_100, 0, u32::MAX][usize::try_from(sequence.next() % 4).unwrap_or(0)];
        let mut line = device::Device::<4>::new(rate);
        let reports = 1 + sequence.next() % 12;
        write!(out, "device {rate} {reports}")?;
        let mut results: Vec<i128> = Vec::new();
        let mut position = sequence.next() >> (sequence.next() % 64);
        let mut time = sequence.signed();
        for _ in 0..reports {
            // Mostly a device that goes on, at times one that starts anew
            // or reports something wild.
            match sequence.next() % 10 {
                0 => {
                    position = sequence.next() >> (sequence.next() % 64);
                    time = sequence.signed();
                }
                1 => position = position.saturating_sub(sequence.next() % 1_000),
                2 => {
                    // Backwards timestamp jitter within the restart threshold.
                    let frames = 1 + sequence.next() % 256;
                    position = position.saturating_add(frames);
                    let jitter = i64::try_from(sequence.next() % 2_000_000).unwrap_or(0);
                    time = time.saturating_sub(jitter);
                }
                _ => {
                    let frames = 1 + sequence.next() % 2_048;
                    position = position.saturating_add(frames);
                    let noise = i64::try_from(sequence.next() % 40_001).unwrap_or(0) - 20_000;
                    time = time
                        .saturating_add(i64::try_from(frames).unwrap_or(0) * 20_833)
                        .saturating_add(noise);
                }
            }
            line.observe(position, time);
            let asked = position
                .saturating_add(sequence.next() % 4_096)
                .saturating_sub(1_024);
            write!(out, " {position} {time} {asked}")?;
            match line.when(asked) {
                Some(found) => results.extend([1, i128::from(found)]),
                None => results.extend([0, 0]),
            }
        }
        writeln!(out, " -> {}", join(&results))?;
    }
    Ok(())
}

fn main() -> io::Result<()> {
    let mut out = BufWriter::new(io::stdout().lock());
    saturate_cases(&mut out)?;
    mul_shift_cases(&mut out)?;
    div_floor_cases(&mut out)?;
    relation_cases(&mut out)?;
    packet_cases(&mut out)?;
    presence_cases(&mut out)?;
    receiver_cases(&mut out)?;
    sender_cases(&mut out)?;
    timing_cases(&mut out)?;
    player_cases(&mut out)?;
    report_cases(&mut out)?;
    device_cases(&mut out)?;
    out.flush()
}
