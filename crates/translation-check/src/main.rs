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

use unisono_core::{fixed, relation};

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

fn main() -> io::Result<()> {
    let mut out = BufWriter::new(io::stdout().lock());
    saturate_cases(&mut out)?;
    mul_shift_cases(&mut out)?;
    div_floor_cases(&mut out)?;
    relation_cases(&mut out)?;
    out.flush()
}
