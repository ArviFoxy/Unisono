# The protocol

unisono sends UDP datagrams. All parties of a stream run the same version of
the software, so there is one layout and nothing to negotiate: a datagram of
another version is rejected. Every number is written least significant byte
first.

There are four kinds of datagram: audio from the sender, reports from
receivers, the sender's answers to reports, and requests of receivers for
frames to be sent again. All begin with the same six bytes: the letters
`unis`, the version, and the kind.

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
| 62 | 2 | protection | the protection against loss that the stream has: 0 is none; 1 says that the sender sends a packet again to a receiver that asks for its frames |
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

A receiver sends reports to the sender. A report is padded with zeros to at
least the length of the report plus its needs (85 bytes), or the length of an
audio packet of the stream when larger, so that it meets the delays that an
audio packet meets without truncating its needs. The first 32 bytes say who
reports; the needs of the latest stretches follow them in the padding.

| Offset | Bytes | Field | Meaning |
|---|---|---|---|
| 0 | 4 | magic | the letters `unis` |
| 4 | 1 | version | 1 |
| 5 | 1 | kind | 2 for a report |
| 6 | 2 | stream | which stream of the sender the receiver plays |
| 8 | 8 | timeline | the timeline that the receiver follows |
| 16 | 8 | receiver | a number that tells this receiver from the others |
| 24 | 8 | sequence | the number of this report among the receiver's reports |
| 32 | 8 | newest | the newest stretch whose need is given |
| 40 | 1 | count | how many stretches are given, back from the newest; at most 11 |
| 41 | 4 each | needs | the need of stretch `newest - i` at place `i`, in microseconds (signed); the smallest number, -2^31, if no frame of it arrived |

A stretch is the frames of the timeline whose index, divided by the window
of the packets, is the same: stretches are counted in the index, so they are
the same at every receiver. The need of a frame is the latency at which it
would just have been in time to be played: the level of the frame, less the
time by which it arrived ahead of the receiver's playhead. A stretch's need is
the largest need of a frame of it. Each stretch appears in several reports,
so a lost report loses nothing; the sender keeps, for each stretch, the
largest need over the reports and the receivers, and chooses the level from
that (see the model, section 6.5). Padding of zeros gives no needs, and a
sender reads only as many as are there; entries whose index would fall before
stretch 0 (`count > newest + 1`) are ignored by `parse_needs`.

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
- **The level.** The level and its slope in a packet hold for the frames
  from that packet on. A packet arrives before its frames are played, so
  when the level takes another course at a packet, a slope that begins or
  ends, a receiver goes on playing the frames before that packet as the
  packets before it said, and takes the new course when the position that is
  due reaches the packet. A receiver keeps two such changes, the start and
  the end of a move. At a third it takes the first at once, early by at most
  the time by which packets are ahead of what is played, so a sender that
  wants every frame played at its level changes the course no more than
  twice within that time. The sender of this repository decides on a move
  once for each second of stream.
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

The sender answers every report of its stream that comes from one of its
configured receiver addresses (`--to` / `receivers`) with a datagram of
exactly 32 bytes, sent to the address the report came from. Reports from any
other source address are ignored and counted as ignored datagrams (so unknown
peers cannot steer the level choice or elicit echoes; a receiver whose replies
leave from a different source address than the one the sender targets, such as
an IPv6 temporary address or another interface on a multihomed host, will need
its outgoing address matched or bound).

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
sender; a report tells it the sender's clock against its own, later by the
delay of that report back. At the same moment the two add up to a time there
and back in which the clocks cancel. The receiver keeps the shortest of the
last minute and takes half of it for the path from the sender. How long the
answer itself takes does not matter: it only carries a number. A receiver
sends twenty reports a second for its first five seconds and five a second
after. A receiver that is told the delay of its path sends them as well, for
the needs they carry, and does not measure the path from the answers.

## The request for frames

When the packets of a stream say so in their `protection` field, a receiver
that misses frames asks the sender for them, with a datagram of exactly 32
bytes sent to the address the audio packets come from.

| Offset | Bytes | Field | Meaning |
|---|---|---|---|
| 0 | 4 | magic | the letters `unis` |
| 4 | 1 | version | 1 |
| 5 | 1 | kind | 4 for a request |
| 6 | 2 | stream | which stream of the sender the receiver plays |
| 8 | 8 | timeline | the timeline of the frames |
| 16 | 8 | first | the index of the first frame that is missed |
| 24 | 8 | frames | how many frames from there on are missed |

The sender sends again every packet it still keeps that has one of those
frames, exactly as it was sent before, to the address the request came from,
if that address is one of its receivers; a request from anywhere else gets
nothing, so the sender cannot be made to send a stream to a third party. It
keeps the packets of about the last second. A packet that arrives twice
changes nothing at a receiver.

A receiver finds frames missing when a packet arrives whose first frame is
beyond the frame after the last that arrived. It asks at once and again
every ten milliseconds, until the frames have arrived or the level has
passed since it found them missing, after which they would be too late. Of
a long run it asks only for the frames that the level reaches back to. A
packet that was overtaken on the way is asked for and arrives twice, which
costs one packet.

A packet that is sent again arrives late, and a receiver measures what its
frames needed as for any other packet. The needs that the sender chooses the
level from therefore contain what the repairs need: where packets are lost
often enough, the level settles where the repairs are in time. The model,
section 6.6, gives the comparison that led to this way of protecting a
stream.
