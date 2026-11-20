# Contributing

## Checking a change

`just check` runs the full CI verification suite; see [README.md](README.md)
for what it checks and which tools it requires. Make sure it passes before
considering a change ready.

Whenever you modify `crates/unisono-core`, run `just translate` to regenerate
the Lean translation and verify that all proofs in `lean/Unisono` still pass.

CI also checks dependencies against `deny.toml` for known security advisories,
allowed licences, and approved sources. If `cargo-deny` is installed locally,
run `just dependencies` to execute the same check.

## Requirements

- **Keep `unisono-core` translatable and panic-free.** Follow the Rust subset
  and rules documented in `docs/core-rust.md`.
- **Write falsifiable tests.** Name each test after the failure it catches, and
  derive expected values from the specification or an independent calculation
  rather than copying program output. When a test asserts a quantitative bound,
  pair it with a fault-injection test demonstrating that the bound can fail.
- **Back behavioural claims with proofs or tests.** Keep `docs/model.md`
  explicit about which claims are proved in Lean and which are not.
- **Keep real-time paths lock-free and allocation-free.** Code running on
  real-time threads must not allocate, lock, or enter the kernel; see
  `docs/realtime.md`.
- **Keep documentation in sync with code.** Update `docs/protocol.md` in the
  same commit as any wire-format change.

## Commits

Write commit messages in full sentences explaining what changed and why. Keep
each commit passing `just check` on its own so changes are straightforward to
review and revert.

## Licence

unisono is licensed under the Mozilla Public License 2.0. All contributions
are submitted under the same licence, and every source file must begin with
the MPL-2.0 header.
