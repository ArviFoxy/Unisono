#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Runs the tests of the ALSA device: starts a PipeWire of its own, with
# WirePlumber and a sink that plays to nothing, and runs the ignored tests of
# crates/unisono-alsa, which open the device that PipeWire gives ALSA
# programs, against it, and stops it again. The instance is
# private to this script: its sockets are in a directory of their own, so a
# PipeWire that the host runs is not touched.
#
# It runs as it is on a host with PipeWire, and in the container of
# containers/audio, which `just alsa` builds and runs it in.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
# A short path: the name of a socket may not be longer than 108 bytes.
runtime="$(mktemp -d /tmp/unisono-pw.XXXXXX)"
config="$runtime/config"
mkdir -p "$config/pipewire/pipewire.conf.d"
cat > "$config/pipewire/pipewire.conf.d/unisono-test.conf" <<'CONF'
context.objects = [
    {   factory = adapter
        args = {
            factory.name     = support.null-audio-sink
            node.name        = "unisono-test-sink"
            media.class      = Audio/Sink
            audio.position   = [ FL FR ]
            audio.rate       = 48000
            node.driver      = true
            object.linger    = true
        }
    }
]
CONF

export XDG_RUNTIME_DIR="$runtime" XDG_CONFIG_HOME="$config" PIPEWIRE_RUNTIME_DIR="$runtime"
export DBUS_SESSION_BUS_ADDRESS="disabled:"
pipewire > "$runtime/pipewire.log" 2>&1 &
pipewire_pid=$!
wireplumber > "$runtime/wireplumber.log" 2>&1 &
wireplumber_pid=$!
stop() {
    kill "$wireplumber_pid" "$pipewire_pid" 2> /dev/null || true
    wait "$wireplumber_pid" "$pipewire_pid" 2> /dev/null || true
    rm -rf "$runtime"
}
trap stop EXIT

# The sink is there once PipeWire lists it.
for _ in $(seq 1 50); do
    if pw-cli ls Node 2> /dev/null | grep -q unisono-test-sink; then
        break
    fi
    sleep 0.1
done
if ! pw-cli ls Node 2> /dev/null | grep -q unisono-test-sink; then
    echo "PipeWire did not start; its log:" >&2
    cat "$runtime/pipewire.log" >&2
    exit 1
fi

cd "$root"
# A capture of the device named after the sink records what the sink plays.
export PIPEWIRE_ALSA='{ stream.capture.sink = true }'
cargo test -p unisono-alsa -- --ignored --nocapture --test-threads 1 "$@"
