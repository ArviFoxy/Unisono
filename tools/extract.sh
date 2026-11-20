#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Translates crates/unisono-core to Lean with Charon and Aeneas.
#
#   extract.sh          writes lean/UnisonoCore.lean
#   extract.sh --check  fails if that file differs from a fresh translation
#
# The translation fails if the crate uses a function of the standard library
# that Aeneas has no Lean model for, because such a function would enter the
# proofs as an axiom.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
aeneas="$root/.tools/aeneas"
generated="$root/lean/UnisonoCore.lean"

if [ ! -x "$aeneas/bin/aeneas" ] || [ ! -x "$aeneas/charon/bin/charon" ]; then
    echo "Aeneas is not built; run tools/proof-tools.sh build" >&2
    exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

(
    cd "$root/crates/unisono-core"
    # Charon compiles with its own toolchain, so it gets its own build directory.
    CARGO_TARGET_DIR="$root/target/charon" \
        "$aeneas/charon/bin/charon" cargo --preset=aeneas --dest-file "$work/unisono_core.llbc"
)
"$aeneas/bin/aeneas" -backend lean -all-computable -no-progress-bar \
    -dest "$work/out" "$work/unisono_core.llbc"

if grep -n '^axiom' "$work/out/UnisonoCore.lean" >&2; then
    echo "the translation contains the axioms above" >&2
    exit 1
fi

if [ "${1:-}" = --check ]; then
    if ! diff -u "$generated" "$work/out/UnisonoCore.lean"; then
        echo "lean/UnisonoCore.lean is out of date; run tools/extract.sh" >&2
        exit 1
    fi
else
    cp "$work/out/UnisonoCore.lean" "$generated"
fi
