// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A program in C that sends and receives through the interface for C,
//! compiled with the system's C compiler against the header and the
//! library.

use std::path::PathBuf;
use std::process::Command;

/// The directory that the library is built into for a test: the directory
/// of this test's program.
fn built() -> PathBuf {
    let mut path = std::env::current_exe().expect("this program's path");
    path.pop();
    path
}

#[test]
fn a_program_in_c_sends_and_receives() {
    let built = built();
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let program = built.join(format!("unisono-c-loopback-{}", std::process::id()));
    let compiled = Command::new("cc")
        .args([
            "-std=c99",
            "-D_POSIX_C_SOURCE=200809L",
            "-Wall",
            "-Wextra",
            "-Werror",
        ])
        .arg("-I")
        .arg(source.join("include"))
        .arg(source.join("tests/loopback.c"))
        .arg("-L")
        .arg(&built)
        .arg("-lunisono_c")
        .arg(format!("-Wl,-rpath,{}", built.display()))
        .arg("-o")
        .arg(&program)
        .output()
        .expect("a C compiler called `cc`");
    assert!(
        compiled.status.success(),
        "compiling: {}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let ran = Command::new(&program).output().expect("the program runs");
    let _ = std::fs::remove_file(&program);
    let said = String::from_utf8_lossy(&ran.stdout);
    assert!(
        ran.status.success(),
        "{said}{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    // "of-stream N furthest F": nearly all frames of the last second are of
    // the stream, each within a frame of the one that is due.
    let numbers: Vec<f64> = said
        .split_whitespace()
        .filter_map(|word| word.parse().ok())
        .collect();
    let [of_stream, furthest] = numbers[..] else {
        panic!("the program said: {said}");
    };
    assert!(of_stream > 45_000.0, "{said}");
    assert!(furthest < 1.0, "{said}");
}
