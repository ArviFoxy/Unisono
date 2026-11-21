#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Checks the machine code of the functions that run on the real-time threads.
#
# tools/realtime-check builds the core's real-time functions into one library,
# and tools/realtime-audio builds the full playback and capture cycles (using
# the standard library) into another. This script links each with only what its
# entry points reach and audits the resulting machine code with crates/reachable
# so that neither library can enter the kernel, trap, allocate, panic, or
# branch through an unresolved pointer.
#
# Jump tables are disabled for the audit builds (-max-jump-table-size=0) so
# crates/reachable can fail closed on every indirect branch without allowing
# arbitrary jmp *%reg instructions.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cargo_target="${CARGO_TARGET_DIR:-$root/target}"
target="$cargo_target/realtime"
library="$target/release/libunisono_realtime_check.a"
linked="$target/realtime.so"
audio_target="$cargo_target/realtime-audio"
audit_rustflags="${RUSTFLAGS:+$RUSTFLAGS }-C llvm-args=-max-jump-table-size=0"

link_entries() {
    # $1: static library; $2: output shared object; remaining args: entry symbols.
    local lib="$1" out="$2"
    shift 2
    {
        echo "{ global:"
        for entry in "$@"; do echo "  $entry;"; done
        echo "local: *; };"
    } > "$out.map"
    local roots=()
    for entry in "$@"; do roots+=("-Wl,-u,$entry"); done
    cc -shared -nostdlib -Wl,--gc-sections -Wl,-z,relro,-z,now \
        "-Wl,--version-script=$out.map" "${roots[@]}" -o "$out" "$lib"
}

cargo build --quiet --release --package reachable --target-dir "$cargo_target"
reachable="$cargo_target/release/reachable"

RUSTFLAGS="$audit_rustflags" cargo build --quiet --release \
    --manifest-path "$root/tools/realtime-check/Cargo.toml" --target-dir "$target"

entries_raw="$(nm -g --defined-only "$library")"
entries="$(printf '%s\n' "$entries_raw" | awk '$3 ~ /^realtime_/ { print $3 }' | sort -u)"
if [ -z "$entries" ]; then
    echo "no real-time entry points found in $library" >&2
    exit 1
fi

# shellcheck disable=SC2086
link_entries "$library" "$linked" $entries

failed=0

# rust_eh_personality is named by the tables for unwinding and is not called.
allowed='^(memcpy|memmove|memset|memcmp|bcmp|rust_eh_personality)$'
undefined_raw="$(nm -D --undefined-only "$linked")"
outside="$(printf '%s\n' "$undefined_raw" | awk 'NF >= 2 { print $2 }' | sort -u | grep -v -E "$allowed" || true)"
if [ -n "$outside" ]; then
    echo "the real-time code needs these from outside:" >&2
    echo "$outside" >&2
    failed=1
fi

symbols_raw="$(nm -C "$linked")"
panics="$(printf '%s\n' "$symbols_raw" | grep -i -E 'panic|unwrap_failed|expect_failed|slice_index|bounds_check|rust_begin_unwind' || true)"
if [ -n "$panics" ]; then
    echo "the real-time code can panic:" >&2
    echo "$panics" >&2
    failed=1
fi

# Whole-library scan of the linked core for instructions that enter the kernel.
kernel_entries="$(objdump -d --no-show-raw-insn "$linked" \
    | grep -E ':[[:space:]]+(syscall|sysenter|int[[:space:]]+\$0x80|svc|swi|ecall)\b' || true)"
if [ -n "$kernel_entries" ]; then
    echo "the real-time core contains kernel-entry instructions:" >&2
    echo "$kernel_entries" >&2
    failed=1
fi

# shellcheck disable=SC2086
if ! core_report="$("$reachable" "$linked" $entries)"; then
    echo "the real-time core reaches what it may not" >&2
    failed=1
fi

# Self-test: confirm that a reachable panic path in realtime-check leaves
# `unisono_realtime_code_panicked` undefined after dead-code elimination AND
# that `reachable` itself rejects it.
probe_target="$target/probe"
probe_lib="$probe_target/release/libunisono_realtime_check.a"
probe_so="$probe_target/probe.so"
RUSTFLAGS="$audit_rustflags" cargo build --quiet --release --features panic-probe \
    --manifest-path "$root/tools/realtime-check/Cargo.toml" --target-dir "$probe_target"
link_entries "$probe_lib" "$probe_so" realtime_panic_probe
probe_undef="$(nm -D --undefined-only "$probe_so")"
if ! printf '%s\n' "$probe_undef" | awk 'NF >= 2 { print $2 }' | grep -qx 'unisono_realtime_code_panicked'; then
    echo "the panic self-test did not catch realtime_panic_probe" >&2
    failed=1
fi
if core_probe_out="$("$reachable" "$probe_so" realtime_panic_probe 2>&1)"; then
    echo "reachable did not reject realtime-check's panic probe" >&2
    failed=1
elif ! printf '%s\n' "$core_probe_out" | grep -E -q 'reaches .*(panic|unisono_realtime_code_panicked)'; then
    echo "reachable rejected realtime-check's panic probe for an unexpected reason:" >&2
    echo "$core_probe_out" >&2
    failed=1
fi

# The cycles of the audio threads, which use the standard library: the
# receiver's playback (pump, resampler, concealment) and the sender's capture.
audio_entries="realtime_playback_cycle realtime_capture_cycle"
RUSTFLAGS="$audit_rustflags" cargo build --quiet --release \
    --manifest-path "$root/tools/realtime-audio/Cargo.toml" --target-dir "$audio_target"
# shellcheck disable=SC2086
link_entries "$audio_target/release/libunisono_realtime_audio.a" "$audio_target/audio.so" $audio_entries
# shellcheck disable=SC2086
if ! audio_report="$("$reachable" "$audio_target/audio.so" $audio_entries)"; then
    echo "the cycles of the audio threads reach what they may not" >&2
    failed=1
fi

# Self-test: a path to a panic in the audio library must fail specifically by
# reporting a reached panic symbol (not merely an incidental fallthrough).
RUSTFLAGS="$audit_rustflags" cargo build --quiet --release --features panic-probe \
    --manifest-path "$root/tools/realtime-audio/Cargo.toml" --target-dir "$audio_target/probe"
link_entries "$audio_target/probe/release/libunisono_realtime_audio.a" "$audio_target/probe.so" \
    realtime_panic_probe
if probe_out="$("$reachable" "$audio_target/probe.so" realtime_panic_probe 2>&1)"; then
    echo "the check of the audio threads did not catch realtime_panic_probe" >&2
    failed=1
elif ! printf '%s\n' "$probe_out" | grep -E -q 'reaches .*panic'; then
    echo "the audio panic self-test failed for an unexpected reason:" >&2
    echo "$probe_out" >&2
    failed=1
fi

if [ "$failed" -ne 0 ]; then
    exit 1
fi
echo "audio threads: $audio_report; no panic, no allocator, no library, no kernel entry"
functions="$(nm --defined-only "$linked" | grep -c ' [tT] ')"
echo "real-time code: $core_report ($functions defined functions, $(stat -c %s "$linked") bytes); no kernel entry, no allocator, no panic"
