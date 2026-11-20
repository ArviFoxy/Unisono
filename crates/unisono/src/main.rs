// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The unisono program.
//!
//! `unisono send` captures a signal with a software device and sends it;
//! `unisono receive` receives a stream and plays it on a software device. The
//! software devices run on the host's raw clock, at a rate that can be set,
//! so that two programs on one host behave as two hosts would; with
//! `--clock-offset` and `--clock-skew` each program has a clock of its own
//! too. Audio systems take the devices' place later.

mod exported;
mod options;
mod receiving;
mod sending;

use std::f64::consts::TAU;
use std::process::ExitCode;
use std::str::FromStr;
use std::time::Duration;

use unisono_runtime::clock;

use crate::options::{Options, Wrong};

const HELP: &str = "\
unisono: sends a stream of audio to receivers, or receives one and plays it.

  unisono send --to ADDRESS ...       see `unisono send --help`
  unisono receive --listen ADDRESS    see `unisono receive --help`
";

/// What a software capture device captures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Signal {
    /// The sample of the frame counted as `i` is `(i + 1) / 2^23` on the
    /// first channel and its negative on the others, starting again after
    /// 2^23 frames: a sample says which frame it is.
    Ramp,
    /// A sine of 440 Hz, a tenth of full scale.
    Tone,
    /// Nothing.
    Silence,
}

impl FromStr for Signal {
    type Err = ();

    fn from_str(text: &str) -> Result<Signal, ()> {
        match text {
            "ramp" => Ok(Signal::Ramp),
            "tone" => Ok(Signal::Tone),
            "silence" => Ok(Signal::Silence),
            _ => Err(()),
        }
    }
}

impl Signal {
    /// Fills `frame`, the frame counted as `position` of a device of `rate`
    /// frames a second.
    pub(crate) fn fill(self, position: u64, rate: u32, frame: &mut [f32]) {
        let value = match self {
            Signal::Ramp => {
                // Below 2^23, so exact as a float.
                #[allow(clippy::cast_precision_loss)]
                let step = ((position % 8_388_608) + 1) as f32;
                step / 8_388_608.0
            }
            Signal::Tone => {
                // A count of frames within a day is exact as a float.
                #[allow(clippy::cast_precision_loss)]
                let seconds = (position % (u64::from(rate) * 86_400)) as f64 / f64::from(rate);
                // A sample is rounded to a float on purpose.
                #[allow(clippy::cast_possible_truncation)]
                let sample = (0.1 * (TAU * 440.0 * seconds).sin()) as f32;
                sample
            }
            Signal::Silence => 0.0,
        };
        for (channel, sample) in frame.iter_mut().enumerate() {
            *sample = if channel == 0 { value } else { -value };
        }
    }
}

/// What runs a command.
type Command = fn(&Options) -> Result<(), Wrong>;

/// Sleeps until the raw clock reads `time`, or for 2 ms at most, so that a
/// loop looks at its work often enough.
pub(crate) fn sleep_until(time: i64) {
    let wait = time.saturating_sub(clock::raw()).clamp(0, 2_000_000);
    std::thread::sleep(Duration::from_nanos(wait.unsigned_abs()));
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let Some((command, rest)) = arguments.split_first() else {
        eprint!("{HELP}");
        return ExitCode::from(2);
    };
    let (known, help, run): (&[&str], &str, Command) = match command.as_str() {
        "send" => (sending::OPTIONS, sending::HELP, sending::run),
        "receive" => (receiving::OPTIONS, receiving::HELP, receiving::run),
        "--help" | "help" => {
            print!("{HELP}");
            return ExitCode::SUCCESS;
        }
        _ => {
            eprint!("there is no command `{command}`\n\n{HELP}");
            return ExitCode::from(2);
        }
    };
    if rest.iter().any(|argument| argument == "--help") {
        print!("{help}");
        return ExitCode::SUCCESS;
    }
    let result = Options::parse(rest, known).and_then(|options| {
        clock::shift(
            options.get("clock-offset", 0)?,
            options.get("clock-skew", 0)?,
        );
        run(&options)
    });
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(wrong) => {
            eprintln!("unisono {command}: {wrong}");
            ExitCode::from(2)
        }
    }
}
