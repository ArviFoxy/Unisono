// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The command line: options of the form `--name value`, each at most once
//! unless it is said to repeat.

use std::collections::HashMap;
use std::fmt;
use std::net::SocketAddr;
use std::str::FromStr;

/// What is wrong with a command line.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Wrong(pub(crate) String);

impl fmt::Display for Wrong {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// The options of a command line, by name.
pub(crate) struct Options {
    values: HashMap<String, Vec<String>>,
}

impl Options {
    /// The options in `arguments`, of which every name is in `known`.
    pub(crate) fn parse(arguments: &[String], known: &[&str]) -> Result<Options, Wrong> {
        let mut values: HashMap<String, Vec<String>> = HashMap::new();
        let mut rest = arguments.iter();
        while let Some(argument) = rest.next() {
            let Some(name) = argument.strip_prefix("--") else {
                return Err(Wrong(format!("expected an option, found `{argument}`")));
            };
            if !known.contains(&name) {
                return Err(Wrong(format!("there is no option `--{name}`")));
            }
            let Some(value) = rest.next() else {
                return Err(Wrong(format!("`--{name}` needs a value")));
            };
            values
                .entry(name.to_string())
                .or_default()
                .push(value.clone());
        }
        Ok(Options { values })
    }

    /// Every value given for `name`.
    pub(crate) fn all(&self, name: &str) -> &[String] {
        self.values.get(name).map_or(&[], Vec::as_slice)
    }

    /// The value of `name` read as a `T`, if it is given; it may be given
    /// once.
    pub(crate) fn one<T: FromStr>(&self, name: &str) -> Result<Option<T>, Wrong> {
        match self.all(name) {
            [] => Ok(None),
            [value] => value
                .parse()
                .map(Some)
                .map_err(|_| Wrong(format!("`--{name} {value}` is not a value it takes"))),
            _ => Err(Wrong(format!("`--{name}` is given more than once"))),
        }
    }

    /// The value of `name`, or `default` when it is not given.
    pub(crate) fn get<T: FromStr>(&self, name: &str, default: T) -> Result<T, Wrong> {
        Ok(self.one(name)?.unwrap_or(default))
    }

    /// The value of `name`, which must be given.
    pub(crate) fn need<T: FromStr>(&self, name: &str) -> Result<T, Wrong> {
        self.one(name)?
            .ok_or_else(|| Wrong(format!("`--{name}` must be given")))
    }

    /// Every value of `name`, read as addresses.
    pub(crate) fn addresses(&self, name: &str) -> Result<Vec<SocketAddr>, Wrong> {
        self.all(name)
            .iter()
            .map(|value| {
                value
                    .parse()
                    .map_err(|_| Wrong(format!("`--{name} {value}` is not an address")))
            })
            .collect()
    }
}
