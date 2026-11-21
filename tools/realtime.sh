#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Checks the machine code of the functions that run on the real-time threads.
#
# tools/realtime-check builds those functions into one library. This script
# links them with everything they reach and nothing else, and fails unless
# the result
#
#   - needs nothing from outside but the functions that copy and fill memory,
#     so it calls no allocator, no lock and no other library;
#   - contains no instruction that enters the kernel;
#   - contains none of the machinery of a panic, so no path in it panics;
#
# and unless the sources of the core, outside their tests, are free of trait
# objects and pointers to functions, so that the code that was inspected is
# all the code these functions can run.
#
# The check is of the code as compiled for this machine, with the options in
# tools/realtime-check/Cargo.toml.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
target="$root/target/realtime"
library="$target/release/libunisono_realtime_check.a"
linked="$target/realtime.so"

cargo build --quiet --release \
    --manifest-path "$root/tools/realtime-check/Cargo.toml" --target-dir "$target"

entries="$(nm -g --defined-only "$library" 2>/dev/null | awk '$3 ~ /^realtime_/ { print $3 }' | sort -u)"
if [ -z "$entries" ]; then
    echo "no real-time entry points found in $library" >&2
    exit 1
fi

# Only the entry points are kept as roots; what they do not reach is dropped.
{
    echo "{ global:"
    for entry in $entries; do echo "  $entry;"; done
    echo "local: *; };"
} > "$target/exports.map"
roots=()
for entry in $entries; do roots+=("-Wl,-u,$entry"); done
cc -shared -nostdlib -Wl,--gc-sections "-Wl,--version-script=$target/exports.map" \
    "${roots[@]}" -o "$linked" "$library"

failed=0

# rust_eh_personality is named by the tables for unwinding and is not called.
allowed='^(memcpy|memmove|memset|memcmp|bcmp|rust_eh_personality)$'
outside="$(nm -D --undefined-only "$linked" | awk '{ print $2 }' | sort -u | grep -v -E "$allowed" || true)"
if [ -n "$outside" ]; then
    echo "the real-time code needs these from outside:" >&2
    echo "$outside" >&2
    failed=1
fi

panics="$(nm -C "$linked" | grep -i -E 'panic|unwrap_failed|expect_failed|slice_index|bounds_check|rust_begin_unwind' || true)"
if [ -n "$panics" ]; then
    echo "the real-time code can panic:" >&2
    echo "$panics" >&2
    failed=1
fi

code="$(objdump -d "$linked")"
kernel="$(echo "$code" | grep -w -E 'syscall|sysenter|svc|int +\$0x80' || true)"
if [ -n "$kernel" ]; then
    echo "the real-time code enters the kernel:" >&2
    echo "$kernel" >&2
    failed=1
fi

# The machine code calls the functions it names through a table of addresses,
# so a call through a pointer cannot be told from those by its instruction.
# It is excluded at the source instead: outside its tests the core has no
# trait object and no pointer to a function, so every call in it is to a
# function that the compiler knows, and all of those are in the library that
# was inspected.
pointers="$(find "$root/crates/unisono-core/src" -type f -name '*.rs' | sort | while IFS= read -r file; do
    awk '
        function strip(line,    out, i, c, nextc, n, in_str, esc) {
            out = ""
            n = length(line)
            in_str = 0
            esc = 0
            for (i = 1; i <= n; i++) {
                c = substr(line, i, 1)
                nextc = (i < n) ? substr(line, i + 1, 1) : ""
                if (blk_depth > 0) {
                    if (c == "/" && nextc == "*") { blk_depth++; i++ }
                    else if (c == "*" && nextc == "/") { blk_depth--; i++ }
                } else if (in_str) {
                    if (esc) { esc = 0 }
                    else if (c == "\\") { esc = 1 }
                    else if (c == "\"") { in_str = 0 }
                } else {
                    if (c == "/" && nextc == "/") {
                        break
                    } else if (c == "/" && nextc == "*") {
                        blk_depth++
                        i++
                    } else if (c == "\"") {
                        in_str = 1
                        out = out " "
                    } else {
                        out = out c
                    }
                }
            }
            return out
        }
        function brace_delta(s,    t, opens, closes) {
            t = s; opens = gsub(/\{/, "", t)
            t = s; closes = gsub(/\}/, "", t)
            return opens - closes
        }
        BEGIN { skip_pending = 0; skip_depth = 0; blk_depth = 0 }
        {
            code = strip($0)
            if (skip_depth > 0) {
                skip_depth += brace_delta(code)
                if (skip_depth < 0) skip_depth = 0
                next
            }
            if (skip_pending) {
                if (code ~ /^[[:space:]]*$/ || code ~ /^[[:space:]]*#\[/) next
                if (code ~ /\{/) {
                    skip_depth = brace_delta(code)
                    if (skip_depth < 0) skip_depth = 0
                    skip_pending = 0
                } else if (code ~ /;/) {
                    skip_pending = 0
                }
                next
            }
            if (code ~ /^[[:space:]]*#\[cfg\(test\)\]/) {
                rest = code
                sub(/^[[:space:]]*#\[cfg\(test\)\]/, "", rest)
                if (rest ~ /\{/) {
                    skip_depth = brace_delta(rest)
                    if (skip_depth < 0) skip_depth = 0
                } else if (rest ~ /;/) {
                    # single-line test item
                } else {
                    skip_pending = 1
                }
                next
            }
            print FILENAME ":" FNR ": " code
        }
    ' "$file"
done | grep -E '\bdyn\b|\bfn[[:space:]]*\(' || true)"
if [ -n "$pointers" ]; then
    echo "the core calls through a pointer:" >&2
    echo "$pointers" >&2
    failed=1
fi

# Self-test: confirm that a reachable panic path actually fails the check by
# leaving `unisono_realtime_code_panicked` undefined after dead-code elimination.
probe_target="$target/probe"
probe_lib="$probe_target/release/libunisono_realtime_check.a"
probe_so="$probe_target/probe.so"
cargo build --quiet --release --features panic-probe \
    --manifest-path "$root/tools/realtime-check/Cargo.toml" --target-dir "$probe_target"
printf '{ global:\n  realtime_panic_probe;\nlocal: *; };\n' > "$probe_target/exports.map"
cc -shared -nostdlib -Wl,--gc-sections "-Wl,--version-script=$probe_target/exports.map" \
    -Wl,-u,realtime_panic_probe -o "$probe_so" "$probe_lib"
if ! nm -D --undefined-only "$probe_so" | awk '{ print $2 }' | grep -qx 'unisono_realtime_code_panicked'; then
    echo "the panic self-test did not catch realtime_panic_probe" >&2
    failed=1
fi

# The cycles of the audio threads, which use the standard library: the
# receiver's playback, with the pump, the resampler and the concealment, and
# the sender's capture. The standard library's start-up code is in any
# library made with it, so here the check follows the calls from the entry
# points (tools/reachable.py).
audio_target="$root/target/realtime-audio"
audio_entries="realtime_playback_cycle realtime_capture_cycle"
link_audio() {
    # $1: the library; $2: the shared object; the rest: its entry points.
    local library="$1" linked_audio="$2"
    shift 2
    {
        echo "{ global:"
        for entry in "$@"; do echo "  $entry;"; done
        echo "local: *; };"
    } > "$linked_audio.map"
    local roots=()
    for entry in "$@"; do roots+=("-Wl,-u,$entry"); done
    cc -shared -nostdlib -Wl,--gc-sections "-Wl,--version-script=$linked_audio.map" \
        "${roots[@]}" -o "$linked_audio" "$library"
}
cargo build --quiet --release \
    --manifest-path "$root/tools/realtime-audio/Cargo.toml" --target-dir "$audio_target"
# shellcheck disable=SC2086
link_audio "$audio_target/release/libunisono_realtime_audio.a" "$audio_target/audio.so" $audio_entries
# shellcheck disable=SC2086
if ! audio_report="$(python3 "$root/tools/reachable.py" "$audio_target/audio.so" $audio_entries)"; then
    echo "the cycles of the audio threads reach what they may not" >&2
    failed=1
fi

# Self-test: a path to a panic in the same kind of library fails the check.
cargo build --quiet --release --features panic-probe \
    --manifest-path "$root/tools/realtime-audio/Cargo.toml" --target-dir "$audio_target/probe"
link_audio "$audio_target/probe/release/libunisono_realtime_audio.a" "$audio_target/probe.so" \
    realtime_panic_probe
if python3 "$root/tools/reachable.py" "$audio_target/probe.so" realtime_panic_probe > /dev/null 2>&1; then
    echo "the check of the audio threads did not catch realtime_panic_probe" >&2
    failed=1
fi

if [ "$failed" -ne 0 ]; then
    exit 1
fi
echo "audio threads: $audio_report; no panic, no allocator, no library, no kernel entry"
functions="$(nm --defined-only "$linked" | grep -c ' [tT] ')"
echo "real-time code: $(echo "$entries" | wc -w) entry points, $functions functions, $(stat -c %s "$linked") bytes; no kernel entry, no allocator, no panic"
