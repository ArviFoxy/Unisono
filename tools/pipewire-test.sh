#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Runs the ignored tests of crates/unisono-pipewire against a private PipeWire
# instance (started by tools/with-pipewire.sh).
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

run_tests() {
    cargo build --package unisono --features pipewire
    UNISONO_PROGRAM="$(cargo metadata --format-version 1 --no-deps \
        | sed 's/.*"target_directory":"\([^"]*\)".*/\1/')/debug/unisono"
    export UNISONO_PROGRAM
    cargo test -p unisono-pipewire -- --ignored --nocapture --test-threads 1 "$@"
}

if [[ "${UNISONO_INSIDE_PIPEWIRE:-}" == "1" ]]; then
    run_tests "$@"
else
    UNISONO_INSIDE_PIPEWIRE=1 exec "$root/tools/with-pipewire.sh" "$0" "$@"
fi
