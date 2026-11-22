#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Starts an isolated PipeWire + WirePlumber instance with a null audio sink
# named `unisono-test-sink`, executes the given command, and tears the instance
# down on exit without touching any host PipeWire session.
set -euo pipefail

# A short path: UNIX socket paths must not exceed 108 bytes.
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

"$@"
