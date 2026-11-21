# The targets other than the host's that every crate must compile for.
targets := "aarch64-apple-darwin aarch64-unknown-linux-musl armv7-unknown-linux-gnueabi x86_64-unknown-linux-musl"

# List the recipes.
default:
    @just --list

# Everything that continuous integration runs.
check: sizes format-check lint test targets realtime cost translation prove translation-check spec-check spec

# No file of the repository is larger than a megabyte: the largest by far is
# the translation of the core, a quarter of that.
sizes:
    @git ls-files -z | xargs -0 du --bytes | awk '$1 > 1048576 { print "too large: " $2; large = 1 } END { exit large }'

# Build the specification of the problem as a PDF and copy it to
# docs/specification.pdf, the copy kept in the repository. The PDF records the
# SHA-256 of its source. The build fails on any LaTeX warning, such as a line
# that runs into the margin.
spec:
    latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=target/spec -usepretex='\def\specsource{'"$(sha256sum docs/specification.tex | cut -d' ' -f1)"'}' docs/specification.tex
    @! grep -E "Warning|Overfull|Underfull" target/spec/specification.log
    cp target/spec/specification.pdf docs/specification.pdf

# The PDF of the specification in the repository is built from the current
# source.
spec-check:
    @pdfinfo docs/specification.pdf | grep -q "$(sha256sum docs/specification.tex | cut -d' ' -f1)" || { echo "docs/specification.pdf is not built from the current docs/specification.tex: run just spec"; exit 1; }

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

# Compile every crate for every target platform. The crates for PipeWire and
# ALSA build against the system's libraries and are left out; the program
# does not need them. On musl the C runtime is linked statically by default,
# and a shared library cannot be built that way, so the C interface, which
# is also built as a shared library, is checked there with the C runtime
# linked dynamically.
targets:
    for target in {{ targets }}; do cargo check --workspace --exclude unisono-pipewire --exclude unisono-alsa --exclude unisono-c --target "$target" || exit 1; done
    for target in {{ targets }}; do case "$target" in *-musl) RUSTFLAGS="${RUSTFLAGS:-} -C target-feature=-crt-static" cargo check --package unisono-c --target "$target" || exit 1 ;; *) cargo check --package unisono-c --target "$target" || exit 1 ;; esac; done

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

# The tests against a running PipeWire, in the container of
# containers/audio. Needs docker; continuous integration runs it too.
pipewire:
    tools/container.sh audio tools/pipewire-test.sh

# The tests of the ALSA device, against the device that PipeWire gives ALSA
# programs, in the container of containers/audio. Needs docker; continuous
# integration runs it too.
alsa:
    tools/container.sh audio tools/alsa-test.sh

# Hold the dependencies against deny.toml: known vulnerabilities, licences
# and sources. Needs cargo-deny; continuous integration runs it too.
dependencies:
    cargo deny check

