# Security

## Reporting a vulnerability

Report security issues privately using "Report a vulnerability" under the
Security tab on GitHub. Please do not open a public issue.

unisono is in early development and has no releases yet, so there are no
supported version branches to list. Reports are evaluated against the current
`main` branch.

## Threat model

Incoming datagrams are untrusted and may contain arbitrary bytes. Parsing or
handling a datagram must never crash a sender or receiver, access memory out of
bounds, or leave a receiver wedged in an unrecoverable state. For
`unisono-core`, these properties are formally proved in Lean (`docs/model.md`,
`lean/Unisono`): every core function terminates without panicking on all inputs
and states, and a receiver always recovers to follow a continuing stream. Any
input that violates these guarantees is a security vulnerability.

## Out of scope

Packets are neither authenticated nor encrypted. Any host able to send
datagrams to a receiver can inject audio, and any host able to observe the
network can listen to the stream. unisono is designed for networks whose hosts
are trusted.
