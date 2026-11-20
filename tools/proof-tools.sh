#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Puts Aeneas at the pinned commit into .tools/aeneas.
#
#   proof-tools.sh fetch   only the checkout: its Lean library is what the
#                          proofs in lean/ build against
#   proof-tools.sh build   also builds the translator and the Charon it pins;
#                          needs opam, rustup and a C toolchain
#
# Running it again does nothing once the checkout and the build are current.
set -euo pipefail

AENEAS_REV=2e3d4488280bb8a95411db81019a7854a784861f
OCAML_VERSION=5.3.0

mode="${1:-build}"
root="$(cd "$(dirname "$0")/.." && pwd)"
dir="$root/.tools/aeneas"
built="$dir/.built-commit"

mkdir -p "$root/.tools"
if [ ! -d "$dir/.git" ]; then
    git clone --quiet https://github.com/AeneasVerif/aeneas "$dir"
fi
if [ "$(git -C "$dir" rev-parse HEAD)" != "$AENEAS_REV" ]; then
    git -C "$dir" fetch --quiet origin
    git -C "$dir" checkout --quiet "$AENEAS_REV"
fi
if [ "$mode" = fetch ]; then
    exit 0
fi
if [ -f "$built" ] && [ "$(cat "$built")" = "$AENEAS_REV" ]; then
    exit 0
fi

cd "$dir"

# Charon, at the commit this Aeneas pins: the program that reads the Rust, and
# the OCaml library that Aeneas compiles from source.
charon_rev="$(tail -1 charon-pin)"
if [ ! -d charon/.git ]; then
    git clone --quiet --recurse-submodules https://github.com/AeneasVerif/charon charon
fi
if [ "$(git -C charon rev-parse HEAD)" != "$charon_rev" ]; then
    git -C charon fetch --quiet origin
    git -C charon checkout --quiet "$charon_rev"
fi
make -C charon build-charon-rust charon-ml/src/CharonVersion.ml

if [ ! -d "${OPAMROOT:-$HOME/.opam}" ]; then
    opam init --bare --no-setup --yes
fi
if [ ! -d _opam ]; then
    opam switch create . "$OCAML_VERSION" --no-install --yes
fi
eval "$(opam env --switch=. --set-switch)"
opam install ./src ./charon/charon.opam ./charon/name_matcher_parser.opam --deps-only --yes
make

echo "$AENEAS_REV" > "$built"
