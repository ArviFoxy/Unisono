// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The pieces of the Prometheus text format: names, escaping and numbers.

use std::fmt::{self, Display, Formatter};

/// Whether `name` is `[a-zA-Z_:][a-zA-Z0-9_:]*`, the form of a metric name.
pub(crate) fn is_metric_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == b'_' || first == b':')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b':')
}

/// Whether `name` is `[a-zA-Z_][a-zA-Z0-9_]*` and does not begin with `__`,
/// which Prometheus keeps for its own labels.
pub(crate) fn is_label_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && !name.starts_with("__")
}

/// Appends a help text as a `# HELP` line carries it.
pub(crate) fn push_help(line: &mut String, help: &str) {
    for character in help.chars() {
        match character {
            '\\' => line.push_str("\\\\"),
            '\n' => line.push_str("\\n"),
            other => line.push(other),
        }
    }
}

/// Appends a label value as it stands between the quotes of a sample line.
pub(crate) fn push_label_value(line: &mut String, value: &str) {
    for character in value.chars() {
        match character {
            '\\' => line.push_str("\\\\"),
            '"' => line.push_str("\\\""),
            '\n' => line.push_str("\\n"),
            other => line.push(other),
        }
    }
}

/// The labels of a sample line with their braces, or nothing when there are
/// no labels.
pub(crate) struct Braced<'a>(pub &'a str);

impl Display for Braced<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            Ok(())
        } else {
            write!(f, "{{{}}}", self.0)
        }
    }
}

/// A floating-point number as the text format writes it.
///
/// A finite number is written with the fewest digits that give the same
/// number back, and without an exponent.
pub(crate) struct Number(pub f64);

impl Display for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0.is_nan() {
            f.write_str("NaN")
        } else if self.0.is_infinite() {
            f.write_str(if self.0.is_sign_positive() {
                "+Inf"
            } else {
                "-Inf"
            })
        } else {
            write!(f, "{}", self.0)
        }
    }
}
