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

use unisono_core::{fixed, packet, presence, relation};

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
    for a in dividends {
        for b in divisors {
            writeln!(out, "div_floor {a} {b} -> {}", fixed::div_floor(a, b))?;
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
fn fields(header: &packet::Audio) -> [i128; 17] {
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
    ]
}

/// What parsing gives, as numbers: 0 and the fields, or the number of the
/// reason for rejection, its detail, and zeros.
fn parsed(bytes: &[u8]) -> [i128; 18] {
    let mut numbers = [0i128; 18];
    match packet::parse_audio(bytes) {
        Ok(header) => numbers[1..].copy_from_slice(&fields(&header)),
        Err(reason) => {
            let (code, detail) = match reason {
                packet::Rejected::TooShort => (1, 0),
                packet::Rejected::NotUnisono => (2, 0),
                packet::Rejected::Version(version) => (3, version),
                packet::Rejected::Kind(kind) => (4, kind),
                packet::Rejected::Format(format) => (5, format),
                packet::Rejected::Length => (6, 0),
            };
            numbers[0] = code;
            numbers[1] = i128::from(detail);
        }
    }
    numbers
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

/// Headers drawn at random, written and read back, and the same packets with
/// one byte changed, one byte more, and one byte less.
fn packet_cases(out: &mut impl Write) -> io::Result<()> {
    let mut sequence = Sequence(3);
    for _ in 0..150 {
        // Each cast keeps the low bits of a random number, which is the intent.
        #[allow(clippy::cast_possible_truncation)]
        let header = packet::Audio {
            stream: sequence.next() as u16,
            timeline: sequence.next(),
            index: sequence.next(),
            capture: sequence.signed(),
            rate: sequence.next() as u32,
            frames: (sequence.next() % 4) as u16,
            channels: (sequence.next() % 4) as u8,
            format: if sequence.next().is_multiple_of(2) {
                packet::Format::Signed16
            } else {
                packet::Format::Signed24
            },
            level: sequence.signed(),
            level_slope: sequence.signed() as i32,
            span: sequence.next() as u32,
            window: sequence.next() as u32,
            flags: sequence.next() as u16,
            protection: sequence.next() as u16,
            stamped_index: sequence.next(),
            stamped_departure: sequence.signed(),
            drift: sequence.signed() as i32,
        };
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
        let mut changed = good.to_vec();
        let place = usize::try_from(sequence.next() % 84).unwrap_or(0);
        changed[place] ^= 1 << (sequence.next() % 8);
        writeln!(
            out,
            "parse_audio {} -> {}",
            bytes_of(&changed),
            join(&parsed(&changed))
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

fn main() -> io::Result<()> {
    let mut out = BufWriter::new(io::stdout().lock());
    saturate_cases(&mut out)?;
    mul_shift_cases(&mut out)?;
    div_floor_cases(&mut out)?;
    relation_cases(&mut out)?;
    packet_cases(&mut out)?;
    presence_cases(&mut out)?;
    out.flush()
}
