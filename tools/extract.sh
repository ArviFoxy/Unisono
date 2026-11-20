#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Translates crates/unisono-core to Lean with Charon and Aeneas.
#
#   extract.sh          writes lean/UnisonoCore/Types.lean and Funs.lean
#   extract.sh --check  fails if those files differ from a fresh translation
#
# The translation fails if the crate uses a function of the standard library
# that Aeneas has no Lean model for, because such a function would enter the
# proofs as an axiom.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
aeneas="$root/.tools/aeneas"
generated="$root/lean/UnisonoCore"

if [ ! -x "$aeneas/bin/aeneas" ] || [ ! -x "$aeneas/charon/bin/charon" ]; then
    echo "Aeneas is not built; run tools/proof-tools.sh build" >&2
    exit 1
fi

# Every function of the core is translated. Only what a type derives may
# depend on whether the crate is being translated.
hidden="$(grep -rn 'cfg(not(translating))' "$root/crates/unisono-core/src" | grep -v 'cfg_attr(not(translating), derive(' || true)"
if [ -n "$hidden" ]; then
    echo "the core has code that the translation would not see:" >&2
    echo "$hidden" >&2
    exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

(
    cd "$root/crates/unisono-core"
    # Charon compiles with its own toolchain, so it gets its own build directory.
    # Under `translating` no type of the core derives `Debug`, whose code is
    # no part of what is proved.
    CARGO_TARGET_DIR="$root/target/charon" RUSTFLAGS="--cfg translating" \
        "$aeneas/charon/bin/charon" cargo --preset=aeneas --dest-file "$work/unisono_core.llbc"
)
# The translation is written as two files, the types and the functions. A
# definition of the standard library that the translator has no model for
# would come out in further files, for someone to fill in, or as an axiom;
# the translation is refused if there is either.
"$aeneas/bin/aeneas" -backend lean -all-computable -no-progress-bar -split-files \
    -dest "$work/out" "$work/unisono_core.llbc"

unexpected="$(find "$work/out" -type f ! -name Types.lean ! -name Funs.lean)"
if [ -n "$unexpected" ]; then
    echo "the translation left definitions to be filled in:" >&2
    echo "$unexpected" >&2
    exit 1
fi
if grep -n '^axiom' "$work/out/Types.lean" "$work/out/Funs.lean" >&2; then
    echo "the translation contains the axioms above" >&2
    exit 1
fi

if [ "${1:-}" = --check ]; then
    for file in Types.lean Funs.lean; do
        if ! diff -u "$generated/$file" "$work/out/$file"; then
            echo "lean/UnisonoCore/$file is out of date; run tools/extract.sh" >&2
            exit 1
        fi
    done
else
    mkdir -p "$generated"
    cp "$work/out/Types.lean" "$work/out/Funs.lean" "$generated/"
fi
