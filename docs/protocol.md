# The protocol

unisono sends UDP datagrams. All parties of a stream run the same version of
the software, so there is one layout and nothing to negotiate: a datagram of
another version is rejected. Every number is written least significant byte
first.

This page describes what is built so far: the audio packet. Reports from
receivers, and the datagrams that carry the stamps for the exchange in both
directions, are not specified yet.

## The audio packet

A header of 80 bytes, then the samples: `frames × channels` samples, each of 2
or 3 bytes, frame after frame. A datagram whose length is not exactly that of
the header and the samples it announces is rejected.

Times are in nanoseconds on the sender's raw clock.

| Offset | Bytes | Field | Meaning |
|---|---|---|---|
| 0 | 4 | magic | the letters `unis` |
| 4 | 1 | version | 1 |
| 5 | 1 | kind | 1 for audio |
| 6 | 2 | stream | which stream of the sender |
| 8 | 8 | timeline | which run of the capture device the indices count in; a restart of the device or of the sender starts another |
| 16 | 8 | index | the index of the first frame within the timeline |
| 24 | 8 | capture | when the first frame was captured (signed) |
| 32 | 4 | rate | frames per second |
| 36 | 2 | frames | the number of frames in the packet |
| 38 | 1 | channels | the number of channels |
| 39 | 1 | format | 1: samples of 2 bytes, signed; 2: of 3 bytes, signed |
| 40 | 8 | level | the latency that every receiver holds for the first frame (signed) |
| 48 | 4 | level slope | how the level changes, in nanoseconds per second of stream (signed) |
| 52 | 4 | span | how long a receiver remembers samples for its estimate of the sender's clock, in milliseconds |
| 56 | 4 | window | the number of frames that make up one window of that estimate |
| 60 | 2 | flags | none defined yet |
| 62 | 2 | protection | the protection against loss that the packet carries; 0 is none |
| 64 | 8 | stamped index | the index of the first frame of an earlier packet of this timeline |
| 72 | 8 | stamped departure | when that earlier packet left the sender (signed) |

A sender learns when a packet left only after it has left, so each packet
carries the departure of an earlier one. A receiver that kept the time of
arrival of that earlier packet then has both stamps of it.

The level, the span and the window are the same for every receiver of the
stream. They travel in every packet so that a receiver that has just started,
or that missed packets, holds them at once.
