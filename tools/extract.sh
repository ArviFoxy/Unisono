#!/usr/bin/env bash
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Translates crates/unisono-core to Lean with Charon and Aeneas.
#
#   extract.sh           writes lean/UnisonoCore/Types.lean and Funs.lean when
#                        missing or out of date with crates/unisono-core
#   extract.sh --force   always runs a fresh translation
#
# The translation fails if the crate uses a function of the standard library
# that Aeneas has no Lean model for, because such a function would enter the
# proofs as an axiom.
set -euo pipefail

force=0
case "${1:-}" in
    "") ;;
    --force) force=1 ;;
    *)
        echo "usage: $0 [--force]" >&2
        exit 2
        ;;
esac
if [ "$#" -gt 1 ]; then
    echo "usage: $0 [--force]" >&2
    exit 2
fi

root="$(cd "$(dirname "$0")/.." && pwd)"
aeneas="$root/.tools/aeneas"
generated="$root/lean/UnisonoCore"
stamp="$generated/.source-hash"

if [ ! -x "$aeneas/bin/aeneas" ] || [ ! -x "$aeneas/charon/bin/charon" ]; then
    echo "Aeneas is not built; run tools/proof-tools.sh build" >&2
    exit 1
fi

# Every function of the core is translated. Only what a type derives may
# depend on whether the crate is being translated; reject any other
# non-comment mention of `translating` (including nested `cfg(all(...))`).
hidden="$(grep -rn '\btranslating\b' "$root/crates/unisono-core/src" \
    | grep -v -E '^[^:]+:[0-9]+:[[:space:]]*//' \
    | grep -v -E '^[^:]+:[0-9]+:[[:space:]]*#\[cfg_attr\(not\(translating\), derive\([A-Za-z, ]+\)\)\][[:space:]]*$' || true)"
if [ -n "$hidden" ]; then
    echo "the core has code that the translation would not see:" >&2
    echo "$hidden" >&2
    exit 1
fi

source_hash="$(
    {
        for f in \
            "$root/Cargo.toml" \
            "$root/Cargo.lock" \
            "$root/crates/unisono-core/Cargo.toml" \
            "$root/tools/proof-tools.sh" \
            "$root/tools/extract.sh"; do
            printf '%s\n' "${f#"$root/"}"
            sha256sum "$f"
        done
        find "$root/crates/unisono-core/src" -type f | LC_ALL=C sort | while IFS= read -r f; do
            printf '%s\n' "${f#"$root/"}"
            sha256sum "$f"
        done
    } | sha256sum | cut -d' ' -f1
)"

if [ "$force" -eq 0 ] \
    && [ -f "$generated/Types.lean" ] \
    && [ -f "$generated/Funs.lean" ] \
    && [ -f "$stamp" ] \
    && [ "$(cat "$stamp")" = "$source_hash" ]; then
    exit 0
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
if grep -n -E '^[[:space:]]*((private|protected|noncomputable)[[:space:]]+)*axiom\b' "$work/out/Types.lean" "$work/out/Funs.lean" >&2; then
    echo "the translation contains the axioms above" >&2
    exit 1
fi

mkdir -p "$generated"
for file in Types.lean Funs.lean; do
    if [ ! -f "$generated/$file" ] || ! cmp -s "$work/out/$file" "$generated/$file"; then
        cp "$work/out/$file" "$generated/$file"
    fi
done
printf '%s\n' "$source_hash" > "$stamp"
