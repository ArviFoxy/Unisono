// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Tells the compiler that `cfg(loom)` is a configuration this crate knows.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(loom)");
}
