# The protocol

unisono sends UDP datagrams. All parties of a stream run the same version of
the software, so there is one layout and nothing to negotiate: a datagram of
another version is rejected. Every number is written least significant byte
first.

There are three kinds of datagram: audio from the sender, reports from
receivers, and the sender's answers to reports. All begin with the same six
bytes: the letters `unis`, the version, and the kind.

## The audio packet

A header of 88 bytes, then the samples: `frames × channels` samples, each of 2
or 3 bytes, frame after frame. A datagram whose length is not exactly that of
the header and the samples it announces is rejected, as is a header with a zero
sample rate or channel count, unknown flag bits, an unsupported protection
scheme, or a `drift` or `level slope` of `-10⁹` or below.

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
| 60 | 2 | flags | bit 0: the packet carries the departure of an earlier packet |
| 62 | 2 | protection | the protection against loss that the packet carries; 0 is none |
| 64 | 8 | stamped index | the index of the first frame of an earlier packet of this timeline, if bit 0 of the flags is set |
| 72 | 8 | stamped departure | when that earlier packet left the sender (signed) |
| 80 | 4 | drift | how much faster than the rate the capture device runs against the sender's clock, in parts per billion (signed) |
| 84 | 4 | clock | identifies the sender's clock instance; changes on host reboot and stays constant across capture-device restarts |

A sender learns when a packet left only after it has left, so each packet
carries the departure of an earlier one. A receiver that kept the time of
arrival of that earlier packet then has both stamps of it.

The capture time and the drift give the capture time of every frame: frame
`index + k` was captured `k × 10⁹ / (rate × (1 + drift × 10⁻⁹))` nanoseconds
after the first. They are the sender's own estimate of its capture device
against its clock.

The level, the span and the window are the same for every receiver of the
stream. They travel in every packet so that a receiver that has just started,
or that missed packets, holds them at once.

## The report

A receiver sends reports to the sender. A report is padded with zeros to the
length of an audio packet of the stream, so that it meets the delays that an
audio packet meets; a receiver reads only the first 32 bytes.

| Offset | Bytes | Field | Meaning |
|---|---|---|---|
| 0 | 4 | magic | the letters `unis` |
| 4 | 1 | version | 1 |
| 5 | 1 | kind | 2 for a report |
| 6 | 2 | stream | which stream of the sender the receiver plays |
| 8 | 8 | timeline | the timeline that the receiver follows |
| 16 | 8 | receiver | a number that tells this receiver from the others |
| 24 | 8 | sequence | the number of this report among the receiver's reports |

What a receiver tells the sender about its margin, for the level, is not in
the report yet.

## What a receiver does with an audio packet

These rules are part of the protocol, because a sender relies on them.

- **Stream.** A receiver is set up for one stream identifier and leaves out
  every packet and every answer of another.
- **Timeline.** A receiver follows one timeline. A packet of another timeline
  is left out, and its timeline is remembered. The next packet makes the
  receiver follow that timeline if it is of that timeline too and either its
  number is larger than that of the followed one, or the followed one has
  been silent for the receiver's time of silence. So one stray packet does
  not move a receiver, and two packets of a sender that started again do.
  A sender that starts again takes a larger timeline number, so that
  receivers follow it at the second packet and not after the silence.
- **Clock.** When the new timeline carries the clock identifier of the one
  before, the receiver keeps its estimate of the sender's clock, since it is
  the same clock. Otherwise it drops the estimate and learns the clock anew.
  It keeps its estimate of the delay of the path in both cases.
- **The index going back.** When every frame of the followed timeline's
  packets has been behind the receiver's playhead for the time of silence,
  the receiver starts anew at the arriving packet.

Where the two numbers come from is the sender's business, under two
conditions. The clock identifier is the same for as long as the sender's
clock runs on, and different after the host has started again and for
another host: a number made from the identity that the system gives each
start of the host serves. The timeline number grows from one start of the
sender's program to the next, also across a start of the host: the time of
day at the start serves, or a number kept on disk. Two senders that share
both numbers cost a receiver that hears both up to one memory span of wrong
timing; they cannot make it stop.

## The answer to a report

The sender answers every report of its stream with a datagram of exactly 32
bytes, sent to the address the report came from.

| Offset | Bytes | Field | Meaning |
|---|---|---|---|
| 0 | 4 | magic | the letters `unis` |
| 4 | 1 | version | 1 |
| 5 | 1 | kind | 3 for an answer |
| 6 | 2 | stream | which stream of the sender this is |
| 8 | 8 | receiver | the receiver whose report this answers |
| 16 | 8 | sequence | the number of the report |
| 24 | 8 | arrival | when the report arrived, on the sender's clock (signed) |

The receiver knows when the report left, on its own clock, so the answer
gives it both stamps of the report. Audio packets tell a receiver its clock
against the sender's, later by the smallest delay of the path from the
sender; reports tell it the sender's clock against its own, later by the
smallest delay of the path back. The two add up to the smallest delay there
and back, and the receiver takes half of it for the path from the sender.
How long the answer itself takes does not matter: it only carries a number.
