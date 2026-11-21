#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Runs the ignored tests of crates/unisono-alsa against PipeWire's ALSA device
# inside a private PipeWire instance (started by tools/with-pipewire.sh).
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

if [[ "${UNISONO_INSIDE_PIPEWIRE:-}" == "1" ]]; then
    # A capture of the device named after the sink records what the sink plays.
    export PIPEWIRE_ALSA='{ stream.capture.sink = true }'
    cargo test -p unisono-alsa -- --ignored --nocapture --test-threads 1 "$@"
else
    UNISONO_INSIDE_PIPEWIRE=1 exec "$root/tools/with-pipewire.sh" "$0" "$@"
fi
