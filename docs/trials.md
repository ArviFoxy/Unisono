# What the first trials found

Three things that the design depends on were tried before it was settled:
whether Aeneas translates the Rust that the core needs, whether a Rust
program can take part in PipeWire's cycle and learn the time of each cycle,
and where the time stamps of packets can come from on Linux. All three ran
on Linux in an unprivileged container, which has no real-time scheduling.
This page records what was found and what the design took from it.

## Translating the core with Aeneas

A test crate of 109 functions, one for each construct the core was to use,
was translated at the commit of Aeneas that `tools/proof-tools.sh` pins; 108
translated. What translates and what does not, and the rules the core follows
as a result, are in `core-rust.md`. Two open reports of the Aeneas project
describe translations that behave differently from the Rust: a write through
a slice taken from an index other than zero, and `Cell` and atomic types used
through a shared reference, which are translated as plain values. The core
uses neither, and every translated function is compared with its Rust on
generated inputs (`crates/translation-check`).

## A Rust program in PipeWire's cycle

Version 0.10.1 of the `pipewire` crate runs a playback stream whose callback
is called in the graph's cycle, and gives for each cycle the time of the
cycle, its count of frames and the delay to the device. The time is on the
system's monotonic clock. With a sink that plays to nothing as the driver,
the reported times lay exactly on a line: they are computed, not measured,
which a test against such a sink has to keep in mind. The callback itself
ran up to a whole cycle late in the container, which has no real-time
scheduling; the reported time was unaffected, which is what the design
relies on: it schedules by the reported time, not by when the callback runs.

The crate exposes neither the stream's control of its rate nor the area in
which PipeWire's resampler takes a rate. PipeWire 1.4 also rounds the input
rate of its resampler to whole hertz, a step of about 21 parts per million at
48,000 frames a second, which is far coarser than the corrections the
regulator makes; version 1.6 keeps 32 fractional bits. unisono does not use
PipeWire's resampler at all: it corrects the rate with its own, and asks of
an audio system only frames, a count of frames and a time for each cycle
(`crates/unisono-runtime/src/audio.rs`). A backend for PipeWire is to use its
C interface where the crate falls short.

## Time stamps of packets on Linux

With UDP over the loopback interface, `SO_TIMESTAMPING` gave a software stamp
for every packet received and, on the socket's queue of errors, for every
packet sent; none was missing. The stamps are on the clock of the time of
day.

- The time from the stamp at sending to the stamp at receiving had a median
  of 0.2 µs and a maximum of 6 µs, also with every processor busy.
- The same measured with stamps that the program took itself, before
  sending and after receiving, under that load: 0.6 ms at the 99th
  percentile and 14 ms at worst. The program is descheduled between its
  stamp and the system call.
- Reading another clock between two readings of the raw monotonic clock
  relates the two to about ±25 ns.
- The monotonic clock ran 25.8 parts per million fast against the raw
  monotonic clock, because the system's time service steers it. A relation
  between the two measured once was 135 µs wrong five seconds later: it has
  to be tracked.
- The clock of the time of day and the monotonic clock differ by an offset
  that changes only when the time of day is set.

What the design took from this: unisono's own time is the raw monotonic
clock, which no service steers; stamps from the kernel are converted to it
through a relation that is measured and tracked (`crates/unisono-runtime/src/clock.rs`);
stamps from the kernel are used wherever the system gives them; and a stamp
the program takes itself is taken so that it errs on the late side, because
the estimate of the sender's clock lies under the samples and an early stamp
pulls it down (`model.md`).

Not tried: the driver-independent stamps that the kernel takes when a packet
is handed to the network device (`SOF_TIMESTAMPING_TX_SCHED`), stamps on real
network interfaces and on Wi-Fi, and other systems. macOS and many Wi-Fi
drivers are said to give no stamps at sending.
