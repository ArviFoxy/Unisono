#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Runs a command in one of the containers of containers/.
#
#   container.sh NAME COMMAND...
#
# Builds the image of containers/NAME/Dockerfile, which docker keeps until it
# changes, and runs COMMAND in a container of it, as the calling user, with
# the repository at /src. What cargo fetches and builds there stays in
# target/container, apart from what the host builds.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"
shift
image="unisono-test-$name"

docker build --quiet --tag "$image" --file "$root/containers/$name/Dockerfile" "$root" > /dev/null
mkdir -p "$root/target/container/cargo"
docker run --rm --name "$image-$$" \
    --user "$(id -u):$(id -g)" \
    --volume "$root:/src" --workdir /src \
    --env CARGO_HOME=/src/target/container/cargo \
    --env CARGO_TARGET_DIR=/src/target/container/target \
    "$image" "$@"
