# Contributing

## Checking a change

`just check` runs everything that continuous integration runs; the README
says what that is and what it needs. A change is ready when it passes.

After a change to `crates/unisono-core`, `just translate` writes the Lean
translation again, and the proofs in `lean/Unisono` have to pass against it.

Continuous integration also holds the dependencies against `deny.toml`: known
vulnerabilities, licences, and where a dependency comes from. `just
dependencies` runs the same where `cargo-deny` is installed.

## What a change needs

- **The core stays in the Rust that translates**, and nothing in it can
  panic: `docs/core-rust.md`.
- **A test names what it would catch.** Its expected values come from the
  specification or an independent calculation, not from what the code printed.
  Where a test holds a number against a bound, a second test with a seeded
  fault shows that the bound can fail.
- **A statement about behaviour is proved or tested, and the documents say
  which.** `docs/model.md` marks what is stated in Lean and what is not.
- **What runs on real-time threads** allocates nothing, takes no lock and
  does not enter the kernel: `docs/realtime.md`.
- **Documents follow the code.** A change to the protocol changes
  `docs/protocol.md` in the same commit.

## Commits

A commit message says what the commit contains and why, in full sentences. A
commit that passes `just check` on its own is easier to review and to revert.

## Licence

unisono is under the Mozilla Public License 2.0. A contribution is made under
the same licence, and every source file starts with its notice.
