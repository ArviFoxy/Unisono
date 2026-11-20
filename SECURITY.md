# Security

## Reporting a vulnerability

Report it in private, through "Report a vulnerability" under the Security tab
of the repository on GitHub. Please do not open a public issue for it.

unisono is in early development and has no releases yet, so there are no
supported versions to list. A report is answered for the current `main`.

## What unisono defends against

A datagram can hold anything. Reading one must never crash a sender or a
receiver, read or write memory out of bounds, or leave a receiver in a state
it does not recover from. For the core this is proved: its functions return
for every input and every state, and a receiver follows the packets that keep
arriving from any state it is in (`docs/model.md`, `lean/Unisono`). A way to
break this is a vulnerability.

## What it does not defend against

Packets are not authenticated and not encrypted. Whoever can send datagrams
to a receiver can make it play something, and whoever can read the network
can hear the stream. unisono is made for a network whose hosts are trusted.
