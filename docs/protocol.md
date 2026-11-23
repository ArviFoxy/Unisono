# The protocol (version 2)

unisono sends User Datagram Protocol (UDP) datagrams. All parties on a stream
run the same wire protocol version (`VERSION = 2`), so there is one layout and
nothing to negotiate: a datagram of any other version is rejected. Every
multi-byte integer is written **little-endian** (least significant byte first),
and signed integers use two's complement.

All datagrams begin with the same 6-byte prefix:

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII letters `unis` (`0x7369_6e75` little-endian `u32`) |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | Datagram kind tag (`1` through `7`) |

Seven datagram kinds are defined in `crates/unisono-core/src/packet.rs`:

| Kind | Name | Direction | Wire size (bytes) | Purpose |
|---|---|---|---|---|
| 1 | `Audio` | sender → receiver | `88 + frames × channels × sample_bytes` | Uncompressed audio frames, schedule, playout level, and optional earlier departure timestamp |
| 2 | `Report` | receiver → sender | `≥ 32` (85 with full needs; padded to `max(85, audio_len)`) | Clock exchange request (`T1`) and stretch latency needs |
| 3 | `Echo` | sender → receiver | `40` (exact) | Four-timestamp reply (`T2`, `T3`) to a `Report` |
| 4 | `Request` | receiver → sender | `32` (exact) | Selective retransmission request for missing frames |
| 5 | `PeerProbe` | receiver → peer | `32` (exact) | Direct peer-to-peer clock exchange probe (`T1`) |
| 6 | `PeerEcho` | peer → receiver | `48` (exact) | Four-timestamp reply (`T2`, `T3`) to a `PeerProbe` |
| 7 | `PeerRelay` | receiver → peers | `29 + 36 × count` (`29..=605`, `count ≤ 16`) | Broadcast of fresh incident link-offset measurements for graph fusion |

**Host identity convention:** within the synchronization protocol, host
identity `0` denotes the stream sender; non-zero `u64` identities denote
receivers.

**Common rejection rules (`packet::Rejected`):** every parser first checks the
6-byte prefix via `packet::kind`: buffers shorter than 6 bytes fail with
`TooShort`, bad magic fails with `NotUnisono`, and any `version != 2` fails
with `Version(v)`. Parsing with the wrong `kind` fails with `Kind(k)`. All
parsers in `unisono-core` are total and panic-free on arbitrary byte slices.

## 1. `Audio` (`kind = 1`, 88-byte header + samples)

An `Audio` datagram consists of an 88-byte header (`HEADER = 88`) followed by
`frames × channels` interleaved signed little-endian pulse-code modulation
(PCM) samples (2 or 3 bytes per sample, frame after frame). Times are in
nanoseconds on the sender's raw monotonic clock.

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `1` (`KIND_AUDIO`) |
| 6 | 2 | `u16` | `stream` | Stream identifier on the sender |
| 8 | 8 | `u64` | `timeline` | Capture-device run in which frame indices count; a restart of the device or sender starts a larger timeline |
| 16 | 8 | `u64` | `index` | Index of the packet's first frame within `timeline` |
| 24 | 8 | `i64` | `capture` | Capture time of the first frame on the sender's clock, in nanoseconds |
| 32 | 4 | `u32` | `rate` | Nominal sample rate, in frames per second (must be non-zero) |
| 36 | 2 | `u16` | `frames` | Number of frames in this packet |
| 38 | 1 | `u8` | `channels` | Number of audio channels (must be non-zero) |
| 39 | 1 | `u8` | `format` | Sample format: `1` = 16-bit signed little-endian (`Signed16`, 2 bytes), `2` = 24-bit signed little-endian (`Signed24`, 3 bytes) |
| 40 | 8 | `i64` | `level` | Playout latency held by all receivers for the packet's first frame, in nanoseconds |
| 48 | 4 | `i32` | `level_slope` | Rate of change of `level`, in nanoseconds per second of stream (must be `≥ -999_999_999`) |
| 52 | 4 | `u32` | `span` | Memory span for the legacy lower-hull clock estimate, in milliseconds |
| 56 | 4 | `u32` | `window` | Number of frames per stretch (used for need reporting and legacy lower-hull estimation) |
| 60 | 2 | `u16` | `flags` | Bit 0 (`FLAG_STAMPED = 1`): packet carries the departure timestamp of an earlier packet; all higher bits must be `0` |
| 62 | 2 | `u16` | `protection` | Loss protection scheme: `0` = none; `1` = `PROTECTION_ON_REQUEST` (sender retransmits kept packets on request) |
| 64 | 8 | `u64` | `stamped_index` | First-frame index of an earlier packet of this timeline (valid when bit 0 of `flags` is set) |
| 72 | 8 | `i64` | `stamped_departure` | Departure time of that earlier packet on the sender's clock, in nanoseconds |
| 80 | 4 | `i32` | `drift` | Capture-device rate offset against the sender's clock, in parts per billion (must be `≥ -999_999_999`) |
| 84 | 4 | `u32` | `clock` | Sender clock instance identifier; constant across capture-device restarts on one host, changes on host reboot |
| 88 | `frames × channels × bytes` | `[u8]` | samples | Interleaved signed little-endian PCM samples |

**Validation rules (`parse_audio`):** a datagram is rejected if:

- `bytes.len() < 88` (`TooShort`);
- magic, version (`2`), or kind (`1`) do not match;
- `format` is not `1` or `2` (`Format(code)`);
- `rate == 0` (`Rate`) or `channels == 0` (`Channels`);
- `(flags & 1) != flags`, i.e., any unknown flag bit is set (`Flags(flags)`);
- `protection > 1` (`Protection(scheme)`);
- `drift < -999_999_999` or `level_slope < -999_999_999` (`Pace`, ensuring `10⁹ + slope > 0`);
- `bytes.len() - 88 != frames × channels × format.bytes()` (`Length`).

A sender learns when a packet left the network interface only after sending it,
so each packet may carry the departure timestamp of an earlier packet (`flags`
bit 0). A receiver that recorded the arrival time of that earlier packet then
holds both timestamps (used by the legacy lower-hull estimator).

The capture timestamp and `drift` determine the capture time of every frame in
the packet: frame `index + k` was captured
`k × 10⁹ / (rate × (1 + drift × 10⁻⁹))` nanoseconds after frame `index`.
`level`, `level_slope`, `span`, and `window` travel in every packet so a newly
started receiver or one recovering from packet loss obtains them immediately.

## 2. `Report` (`kind = 2`, 32-byte header + optional needs + padding)

A receiver sends `Report` datagrams to the stream sender. The first 32 bytes
(`REPORT = 32`) identify the report; the optional trailing needs block
(`NEEDS = 53` bytes when full, bytes `32..85`) carries the receiver's recent
stretch latency needs. The runtime pads every report with trailing zeros to at
least `max(85, audio_packet_len)` bytes (clamped to the outgoing buffer size)
so that reports experience transmission delays comparable to audio packets
without truncating their needs.

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `2` (`KIND_REPORT`) |
| 6 | 2 | `u16` | `stream` | Stream identifier |
| 8 | 8 | `u64` | `timeline` | Timeline currently followed by the receiver |
| 16 | 8 | `u64` | `receiver` | Non-zero receiver identity |
| 24 | 8 | `u64` | `sequence` | Monotonic report sequence number (matched to departure timestamp `T1` when `Echo` returns) |
| 32 | 8 | `u64` | `newest` | *(Optional needs block)* Newest stretch index reported |
| 40 | 1 | `u8` | `count` | *(Optional needs block)* Number of stretch needs present, back from `newest`; at most `RECENT = 11` |
| 41 + 4i | 4 each | `i32` | `needs[i]` | *(Optional needs block, `0 ≤ i < count`)* Largest need of stretch `newest - i`, in microseconds, or `UNKNOWN_NEED = -2³¹` (`i32::MIN`) if no frame of that stretch arrived |

**Validation rules (`parse_report`, `parse_needs`):**

- `parse_report` requires `bytes.len() >= 32` (`TooShort` otherwise) plus valid
  magic, version `2`, and kind `2`. Trailing bytes beyond byte 31 are ignored
  by `parse_report` and decoded separately by `parse_needs`.
- `write_report` rounds any requested length below 32 up to 32 and writes zero
  padding in bytes `32..length`.
- `parse_needs` is infallible: a buffer shorter than 41 bytes or zero-padded
  beyond byte 32 yields `Recent::NONE` (`count = 0`). `count` is clamped to
  `RECENT = 11`, parsing stops early if the buffer ends before all entries, and
  entries whose index would precede stretch 0 (`i > newest`) are ignored.
- `write_needs` returns `false` and leaves the buffer untouched if the buffer
  lacks `32 + 9 + 4 × min(count, 11)` bytes.

A stretch is the set of frames of a timeline sharing the same quotient
`index / window`. The need of a frame is the playout latency at which it would
just have arrived in time to be played (`level` minus arrival margin ahead of
the playhead); a stretch's need is the largest need among its frames. Each
stretch appears in multiple consecutive reports so lost reports lose no
information; the sender retains the maximum need across receivers and chooses a
shared playout level from it.

## 3. What a receiver does with an audio packet

These receiver rules are part of the protocol because the sender relies on
them:

- **Stream.** A receiver is configured for one stream identifier and ignores
  every packet of any other stream.
- **Timeline.** A receiver follows one timeline. A single packet of a different
  timeline is ignored and its timeline identifier remembered. A second packet
  of that timeline causes adoption if its timeline number exceeds the followed
  one, or if the followed timeline has been silent for the receiver's silence
  timeout. A restarted sender picks a larger timeline number so receivers adopt
  it on the second packet without waiting for the silence timeout.
- **Clock.** If a newly adopted timeline carries the same `clock` identifier as
  the previous one, the receiver keeps its sender-clock estimate (same host
  clock). If `clock` changes (sender host reboot or host change), the receiver
  resets its sender-clock estimate and drops relayed sender edges `(0, peer)`,
  while preserving direct peer-to-peer estimates.
- **Playout level.** `level` and `level_slope` apply from the packet's first
  frame onward. Because packets arrive ahead of playback, the receiver holds up
  to two pending level-course changes (the start and end of a ramp) and applies
  each when the due position reaches that packet's `index`. A sender wanting
  every frame played at its planned level issues at most two course changes
  within one lead window (the sender here decides at most once per second of
  stream).
- **Index going backward.** If every frame of the followed timeline's incoming
  packets has lain behind the playhead for the silence timeout, the receiver
  restarts at the arriving packet.

The `clock` identifier must remain constant while the sender's raw clock runs
continuously and change across host reboots or distinct hosts (for example,
derived from the host's boot identifier). The `timeline` number must increase
across sender restarts, including across host reboots (for example, seeded from
wall-clock time or persisted on disk).

## 4. `Echo` (`kind = 3`, exact length 40 bytes)

The sender answers every valid `Report` on its stream arriving from a
configured receiver address (`--to` / `receivers`) with an `Echo` datagram of
exact length `ECHO = 40` bytes sent back to the report's source address.
Reports from unconfigured addresses are ignored and counted as ignored
datagrams.

In version 2, `Echo` carries **both** the sender's arrival timestamp (`T2`) and
departure timestamp (`T3`), expanding the datagram from 32 bytes (v1) to 40
bytes.

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `3` (`KIND_ECHO`) |
| 6 | 2 | `u16` | `stream` | Stream identifier |
| 8 | 8 | `u64` | `receiver` | Identity of the receiver whose report is answered |
| 16 | 8 | `u64` | `sequence` | Sequence number echoed from the `Report` |
| 24 | 8 | `i64` | `arrival` | Sender's clock when the `Report` arrived (`T2`), in nanoseconds |
| 32 | 8 | `i64` | `departure` | Sender's clock when this `Echo` left (`T3`), in nanoseconds |

**Validation rules (`parse_echo`):** `< 40` bytes fails with `TooShort`;
`> 40` bytes fails with `Length` (exact length 40 required), after magic,
version (`2`), and kind (`3`) checks.

**Four-timestamp clock exchange:** matching `Echo.sequence` to the receiver's
recorded `Report` departure timestamp `T1` and combining it with `T2 = arrival`,
`T3 = departure`, and the receiver's local arrival timestamp `T4` yields an
exact Network Time Protocol (NTP)-style four-timestamp exchange
(`unisono_core::min_rtt::ntp_exchange`):

- sender processing time `proc = T3 - T2` (exchange rejected if `proc < 0`);
- round-trip time (RTT) `rtt = (T4 - T1) - (T3 - T2)` (exchange rejected if `rtt < 0`);
- offset estimate `offset = floor(((T2 - T1) + (T3 - T4)) / 2)` estimating
  `sender_clock - receiver_clock` in nanoseconds;
- local-clock midpoint `midpoint = T1 + floor((T4 - T1) / 2)`.

Subtracting `T3 - T2` removes sender turnaround delay from both the round-trip
time and the clock-offset estimate. The receiver feeds valid exchanges into a
deduplicated sliding-window minimum-RTT selector (`MIN_RTT_WINDOW = 8`,
`MIN_RTT_STRIDE = 4`) and two-state Kalman filter. (When configured for the
legacy lower-hull estimator, `Echo.arrival` is used alongside stamped
audio-packet departures as before.)

Default reporting cadence: 20 reports per second (`50 ms`) during startup
(`5 s`), then 5 reports per second (`200 ms`) in steady state (or 4 Hz in
peer-sync probing; see Section 6).

## 5. `Request` (`kind = 4`, exact length 32 bytes)

When `Audio.protection == PROTECTION_ON_REQUEST` (`1`), a receiver detecting
missing frames sends a `Request` datagram of exact length `REQUEST = 32` bytes
to the active sender's address.

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `4` (`KIND_REQUEST`) |
| 6 | 2 | `u16` | `stream` | Stream identifier |
| 8 | 8 | `u64` | `timeline` | Timeline to which the missing frames belong |
| 16 | 8 | `u64` | `first` | Index of the first missing frame |
| 24 | 8 | `u64` | `frames` | Number of missing frames starting at `first` |

**Validation rules (`parse_request`):** `< 32` bytes fails with `TooShort`;
`> 32` bytes fails with `Length` (exact length 32 required), after magic,
version (`2`), and kind (`4`) checks.

The sender checks that the request comes from a configured receiver address on
its stream; requests from unconfigured addresses are ignored so the sender
cannot be used as a reflector. For valid requests, the sender retransmits kept
audio packets overlapping `[first, first + frames)` on `timeline`, oldest
first, up to a per-turn retransmission cap, retaining roughly the last second
of transmitted packets. Duplicate packets are idempotent at the receiver.

A receiver detects a gap when an arriving packet starts beyond the next
expected frame index, requests missing frames immediately, and retries every
`10 ms` until the frames arrive or the playout level has elapsed since the gap
was noticed. For long gaps it requests only frames within one playout level of
the newest packet. Because retransmitted packets carry their original headers,
their arrival margins enter the receiver's reported stretch needs, allowing the
sender's level controller to settle where repairs arrive in time.

## 6. `PeerProbe` (`kind = 5`, exact length 32 bytes)

In peer-assisted synchronization mode, a receiver probes each configured peer
directly with a `PeerProbe` datagram of exact length `PEER_PROBE = 32` bytes,
recording its local departure timestamp `T1` keyed by `sequence`.

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `5` (`KIND_PEER_PROBE`) |
| 6 | 2 | `u16` | `stream` | Stream identifier shared by both receivers |
| 8 | 8 | `u64` | `prober` | Identity of the probing receiver |
| 16 | 8 | `u64` | `target` | Identity of the target peer receiver |
| 24 | 8 | `u64` | `sequence` | Monotonic probe sequence number for matching `PeerEcho` to `T1` |

**Validation rules (`parse_peer_probe`):** `< 32` bytes fails with `TooShort`;
`> 32` bytes fails with `Length` (exact length 32 required), after magic,
version (`2`), and kind (`5`) checks.

Default peer-probing cadence (`SyncSettings::standard`): 20 probes per second
(`50 ms`) staggered across configured peers during the initial `4 s` startup
window, then 4 probes per second (`250 ms`) in steady state.

## 7. `PeerEcho` (`kind = 6`, exact length 48 bytes)

A receiver answering a valid `PeerProbe` from a configured peer replies
immediately with a `PeerEcho` datagram of exact length `PEER_ECHO = 48` bytes
carrying its local probe arrival timestamp (`T2`) and reply departure timestamp
(`T3`).

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `6` (`KIND_PEER_ECHO`) |
| 6 | 2 | `u16` | `stream` | Stream identifier shared by both receivers |
| 8 | 8 | `u64` | `prober` | Identity of the receiver that sent the `PeerProbe` |
| 16 | 8 | `u64` | `responder` | Identity of the responding peer receiver |
| 24 | 8 | `u64` | `sequence` | Probe sequence number echoed from `PeerProbe` |
| 32 | 8 | `i64` | `arrival` | Responder's clock when `PeerProbe` arrived (`T2`), in nanoseconds |
| 40 | 8 | `i64` | `departure` | Responder's clock when this `PeerEcho` left (`T3`), in nanoseconds |

**Validation rules (`parse_peer_echo`):** `< 48` bytes fails with `TooShort`;
`> 48` bytes fails with `Length` (exact length 48 required), after magic,
version (`2`), and kind (`6`) checks.

Upon receiving `PeerEcho` at local timestamp `T4`, the prober looks up `T1` by
`sequence` and evaluates the same four-timestamp exchange `(T1, T2, T3, T4)`
through `ntp_exchange`, estimating `clock(responder) - clock(prober)` via the
peer's sliding-window minimum-RTT selector and per-peer Kalman filter.

## 8. `PeerRelay` (`kind = 7`, 29-byte header + up to 16 × 36-byte edges, max 605 bytes)

To give every receiver a full view of the synchronization graph (so each
receiver can locally solve the graph-Laplacian Best Linear Unbiased Estimator
(BLUE) without a central server), each receiver periodically broadcasts its
fresh incident link measurements to its configured peers in a `PeerRelay`
datagram.

A `PeerRelay` consists of a 29-byte fixed header (`PEER_RELAY_HEADER = 29`)
followed by `count` entries of `RelayEdge` (`RELAY_EDGE = 36` bytes each), with
`count ≤ MAX_RELAY_EDGES = 16`, giving a maximum datagram length of
`29 + 16 × 36 = 605` bytes (`PEER_RELAY_MAX = 605`).

### Fixed header (29 bytes)

| Offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `[u8; 4]` | `magic` | ASCII `unis` |
| 4 | 1 | `u8` | `version` | `2` |
| 5 | 1 | `u8` | `kind` | `7` (`KIND_PEER_RELAY`) |
| 6 | 2 | `u16` | `stream` | Stream identifier |
| 8 | 8 | `u64` | `sender` | Identity of the relaying receiver |
| 16 | 8 | `u64` | `sequence` | Monotonic relay sequence number |
| 24 | 4 | `u32` | `sender_clock_id` | Active stream sender `clock` identifier (`Audio.clock`), fencing relayed sender edges (`from_id = 0`) across sender reboots or switches |
| 28 | 1 | `u8` | `count` | Number of `RelayEdge` entries following the header (`0..=16`) |

### `RelayEdge` entry (36 bytes, entry `i` starts at offset `29 + 36 × i`)

| Relative offset | Bytes | Type | Field | Meaning |
|---|---|---|---|---|
| +0 | 8 | `u64` | `from_id` | Source host identity (`0` = stream sender; non-zero = receiver) |
| +8 | 8 | `u64` | `to_id` | Destination host identity (`0` = stream sender; non-zero = receiver) |
| +16 | 8 | `i64` | `offset_ns` | Estimated clock offset `clock(to_id) - clock(from_id)` at the observation timestamp, in nanoseconds |
| +24 | 8 | `u64` | `variance_ns2` | Estimated measurement variance of `offset_ns` at the observation timestamp, in square nanoseconds (includes any configured static link weight) |
| +32 | 4 | `u32` | `age_ns` | True age `now_ns - last_time_ns` of this observation on the relaying receiver's clock when the relay was built, in nanoseconds (clock-offset-invariant across hosts) |

**Validation rules (`parse_peer_relay`, `write_peer_relay`):**

- `bytes.len() < 29` fails with `TooShort`;
- `count > 16` (`MAX_RELAY_EDGES`) fails with `Length` (and `write_peer_relay`
  returns `None`);
- `bytes.len() < 29 + 36 × count` fails with `TooShort`;
- `bytes.len() != 29 + 36 × count` (trailing bytes) fails with `Length`;
- `count = 0` (29 bytes total) is syntactically valid at the wire layer, though
  `Sync::build_relay` returns `None` when it has zero fresh edges to broadcast.

**Relay generation and ingestion semantics (`unisono_core::sync::Sync`):**

- Default relay broadcast interval: `250 ms` (4 Hz), emitted only when at least
  one direct peer is configured and at least one fresh incident measurement
  exists (age `0 ≤ age ≤ peer_stale_ns`, default `5 s`).
- A relay includes the receiver's fresh sender edge as `(from_id = 0, to_id = self, offset_ns = -(clock(0) - clock(self)))` and each fresh direct peer
  edge as `(from_id = self, to_id = peer, offset_ns = clock(peer) - clock(self))`,
  up to 16 edges (1 sender edge + up to 15 direct peers).
- Carrying `age_ns` instead of an absolute timestamp keeps edge freshness
  invariant to arbitrary host clock offsets: the receiving peer estimates the
  measurement time on its own clock as
  `meas_time_ns = rx_ns - (age_ns + relayer_path_ns)`, where `relayer_path_ns`
  is the estimated one-way path delay from the relayer.
- Duplicate relay sequence numbers from the same peer are ignored. Each
  accepted non-incident edge is canonicalized to `from_id < to_id` (negating
  `offset_ns` when endpoints are swapped) and stored in a bounded relayed-edge
  table (`MAX_RELAY_TABLE = 128`) for local graph BLUE fusion.

## 9. Peer allowlist and Star-mode behavior

Both sender and receivers enforce static configuration allowlists so unknown
hosts cannot inject clock measurements, steer playout latency, or trigger
packet amplification:

- **Sender receiver allowlist:** the sender accepts `Report` and `Request`
  datagrams only from configured receiver socket addresses (`--to` /
  `receivers`) matching its `stream`. Datagrams from any other source address
  are ignored.
- **Star mode (`peer_count == 0`):** when a receiver has no configured peers,
  `Sync` operates strictly in Star mode:
  - it never emits `PeerProbe`, `PeerEcho`, or `PeerRelay` datagrams
    (`next_peer_probe` and `build_relay` always return `None`);
  - all incoming `PeerProbe`, `PeerEcho`, and `PeerRelay` datagrams are
    ignored;
  - `Sync::step` publishes `peer_active = false`, `active_peers = 0`, and
    `diff_var_ns2 = 0`, exporting the direct sender `KalmanFilter` line as
    `common_line`, so playback regulation degenerates identically to
    single-mode Star operation.
- **Peer allowlist (`1..=15` configured peers, `MAX_DIRECT_PEERS = 15`, `MAX_HOSTS = 17`):**
  every direct peer must be configured statically with a non-zero identity
  distinct from `self` and from all other peers (and, in the runtime, paired
  with its allowed socket address):
  - `PeerProbe`: answered with `PeerEcho` only if `probe.stream == stream`,
    `probe.target == self.identity`, and `probe.prober` is in the configured
    peer table (`Sync::on_peer_probe`). Probes from unknown or unconfigured
    identities receive no reply.
  - `PeerEcho`: accepted only if `echo.stream == stream`,
    `echo.prober == self.identity`, `echo.responder` is in the configured peer
    table, and `echo.sequence` matches a recorded in-flight probe departure
    `T1`.
  - `PeerRelay`: accepted only if `relay.stream == stream` and `relay.sender`
    is in the configured peer table. Each `RelayEdge` inside an accepted relay
    is further accepted only if `from_id != to_id`, `variance_ns2 > 0`, neither
    endpoint equals `self.identity` (local direct measurements take precedence
    for incident links), both endpoints are known hosts (`0` or a configured
    peer), and the total transit age `age_ns + relayer_path_ns` does not exceed
    `peer_stale_ns` (default `5 s`).
