# The targets other than the host's that every crate must compile for.
targets := "aarch64-apple-darwin aarch64-unknown-linux-musl armv7-unknown-linux-gnueabi x86_64-unknown-linux-musl"

# List the recipes.
default:
    @just --list

# Everything that continuous integration runs.
check: format-check lint test targets realtime cost translation prove translation-check

# Rewrite the Rust sources in the standard format.
format:
    cargo fmt --all

format-check:
    cargo fmt --all --check

lint:
    cargo clippy --workspace --all-targets -- -D warnings

test: interleavings
    cargo test --workspace

# Check the ring between threads under every interleaving of its two threads.
interleavings:
    RUSTFLAGS="--cfg loom" CARGO_TARGET_DIR=target/loom cargo test --package unisono-runtime --lib --release ring::

# Compile every crate for every target platform.
targets:
    for target in {{ targets }}; do cargo check --workspace --target "$target" || exit 1; done

# Fetch Aeneas and build the translator from Rust to Lean (slow the first time).
proof-tools:
    tools/proof-tools.sh build

# Translate the core to Lean again, after its Rust has changed.
translate: proof-tools
    tools/extract.sh

# Fail if the Lean translation in the repository is not that of the current Rust.
translation: proof-tools
    tools/extract.sh --check

# Check the proofs.
prove:
    tools/proof-tools.sh fetch
    cd lean && lake exe cache get && lake build

# Evaluate the Lean translation on the inputs the Rust was run on, and compare.
translation-check:
    tools/proof-tools.sh fetch
    mkdir -p target
    cargo run --quiet --package translation-check > target/translation-check.txt
    cd lean && lake env lean --run TranslationCheck.lean ../target/translation-check.txt

# Inspect the machine code of the functions that run on real-time threads:
# no kernel entry, no allocator, no panic.
realtime:
    tools/realtime.sh

# Count the instructions of the real-time functions on the inputs that cost
# most, against their budgets, and time them.
cost:
    cargo run --quiet --release --package cycle-cost

# Hold the dependencies against deny.toml: known vulnerabilities, licences
# and sources. Needs cargo-deny; continuous integration runs it too.
dependencies:
    cargo deny check

