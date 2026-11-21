# The problem

This document states the problem that unisono solves, and nothing about how
it solves it. `lean/Unisono/Spec` states the same in Lean; a name in
backquotes is its definition there.

Statements about the problem, such as limits that no solution can beat, and
statements about a solution, such as what it achieves, are made against this
specification and under a model of the world (section 7). A solution is one
whole system, judged by what it achieves for the objectives of section 5.
Whatever it does inside, a schedule, an estimate of a clock, a controller,
who sends what to whom, is the solution's own choice and appears nowhere
here.

## 1. Scope

One sender captures audio from one source. Several speakers play it. Each
speaker is a playback device, driven by a host; a host may drive several
speakers, and the sender's host may drive speakers too. We want every
speaker to play every sample of the source:

- **in synchronisation:** every speaker plays a sample at the same moment;
- **with low latency:** soon after the sample was captured; or, in
  **lip-sync mode**, a target time after it was captured, which the
  application gives;
- **with little rate distortion:** at the speed at which the source was
  captured, changing speed only slowly;
- **with no missed samples:** every output sample is the original sample in
  its place.

Outside the scope:

- correcting for the time sound takes from a speaker to a listener (room
  correction): every speaker is to play a sample at the same moment;
- what a speaker plays instead of a missed sample (concealment): every
  output sample that is not the original counts as missed, whatever it is;
- how well content between two samples is reproduced (the quality of
  resampling);
- devices of different nominal rates: all devices have one nominal rate.

## 2. The world (`World`)

The world is everything that no solution chooses. `World` is one world;
which worlds can happen, and how likely each is, is a model of the world
(section 7).

- **True time** is a real number of seconds (`Time`). No device can read
  it.
- **The capture device** of the sender (`CaptureDevice`) captures frame `n`
  of the source at true time `capture n`; frames are numbered from zero, and
  a frame holds one sample of each channel. It hands the frames to the
  sender's host in blocks: block `b` holds the frames from `first b` to just
  before `first (b + 1)`, and is handed over at true time `handed b`, after
  its last frame is captured. With each frame it reports, as a reading of
  its host's clock, when the frame was captured; the report may be wrong.
- **Speaker `r`** is a playback device (`PlaybackDevice`). Its output sample
  `k` leaves the device, at its output, at true time `out k`. The device
  asks its host for its output samples in blocks: block `b` holds the output
  samples from `first b` to just before `first (b + 1)`, and is asked for at
  true time `asked b`, before its first output sample leaves. With each
  output sample it reports when it will leave, as a reading of its host's
  clock; the report may be wrong.
- **Every host** has a clock (`Clock`): what it reads at each true time. It
  goes forward and does not jump, at a rate of its own.
- **The network** (`Network`) carries messages between any two hosts. A
  message that host `i` sends to host `j` at true time `s`, as its `q`-th
  message to `j`, arrives at true time `deliver i j s q`, or is lost. It
  arrives after it is sent. When and whether it arrives may depend on when
  it is sent and on how many messages went before it on the same way; not
  on what it carries.
- All devices have the same nominal rate (`rate`), frames a second; each
  runs at the rate of its own oscillator.
- The hosts are the sender's host and the speakers' hosts (`hosts`).

Content between two frames is captured, by definition, between their
captures in proportion (`World.captured`): content at position `x`, in
frames, was captured at `capture ⌊x⌋ + (x − ⌊x⌋)·(capture (⌊x⌋ + 1) − capture ⌊x⌋)`.
A speaker may play content at any position, which is how it plays faster or
slower than its device runs.

## 3. What a host observes (`Observation`, `Event`)

A host acts at its events. At each event it observes one of:

- the capture device hands over a block: its frames, each with the
  device's report (at the sender's host only);
- a speaker's device asks for a block: its output samples, each with the
  device's report;
- a message arrives: from which host, its contents, and which frames of the
  source it carries the data of;
- a wake-up that the host asked for comes;

together with the reading of its own clock. Its **view** at an event is the
list of its events so far, each as it saw it: a reading of its own clock and
what it observed. True time is not in the view, and neither is anything that
happens at another host, unless a message brought it.

## 4. What a solution can do (`Action`, `Solution`, `Run`)

At each event a host:

- sends messages to any hosts, with contents of the solution's choosing, and
  with the data of frames of the source that it holds;
- asks to be woken at readings of its clock;
- when a speaker's device asks for a block, says for each of the block's
  output samples what it plays: the source's content at a position, or
  anything else.

A **solution** (`Solution`) says what each host does at each event, given
its view. It may have speakers send messages to each other, have the sender
announce anything to anyone, keep any state it can derive from its view. A
host **holds** a frame of the source when an event so far brought its data:
the capture device's handing over, at the sender, or a message.

Three limits hold whatever the solution:

- **causality:** what a host does at an event depends only on its view;
- **data:** a host sends only frames it holds, and a speaker plays content
  at position `x` only if its host holds the two frames on either side of
  `x` when the device asks for the block (`Consistent.plays`);
- **capacity:** in any second, a host sends any other host at most a given
  number of messages, carrying at most a given number of frames
  (`WithinBudget`). The two numbers are parameters.

A **run** (`Run`) records what happens when a solution runs in a world: each
host's events in order, each with its true time, what the host observed and
why the event happened, and what each speaker played at each output sample.
A record is a run of the solution in the world (`Consistent`) when:

- each host's events come in the order of true time, and no two have the
  same cause;
- each event is what its cause makes it: a block handed over or asked for
  is an event at the time the device says, with the frames or output
  samples of the block and the device's reports; a message is an event at
  the host it was sent to, at the time the network delivers it, with its
  contents; a wake-up is an event when the host's clock reads what was
  asked;
- every block of every device, every message that the network delivers,
  and every wake-up asked for at a later reading is an event;
- what each host does at each event is what the solution says for its view;
- the data limit holds.

A solution is admissible in a world for a capacity when it has a run there
and every run of it stays within the capacity (`Solution.Admissible`).

## 5. The objectives (`Objectives.lean`)

All objectives are measured in true time, from what each speaker plays at
each output sample.

**Going on.** A speaker's playback goes on from output sample `k` to the
next when both play the source and the content advances by more than
nothing and less than two frames (`Continues`): no frame is skipped and none
is played again.

**When a speaker plays a frame.** Speaker `r` plays frame `n` within the
first step that goes on and passes it, between the times at which the
step's two output samples leave, in proportion to where `n` lies between
their contents (`World.playTime`). Call that time `Tᵣ(n)`.

**Latency.** The latency of frame `n` at speaker `r` is `Tᵣ(n) − capture n`
(`World.latency`).

**Synchronisation.** For frame `n`, the squares of the differences
`Tᵣ(n) − Tᵣ'(n)` over all pairs of speakers that play it, divided by the
square of the number of speakers `R` (`World.syncCost`). When every speaker
plays the frame this is the variance of the times at which they play it
(`sum_pairs_eq`). It compares speakers with each other only.

**Low latency.** For frame `n`, its latency summed over the speakers that
play it, divided by `R` (`World.latencyCost`).

**Tracking,** in lip-sync mode, of a target latency `L*(n)` that the
application gives for each frame: for frame `n`, the squares of the
differences between its latency and `L*(n)`, summed over the speakers that
play it, divided by `R` (`World.trackingCost`).

**Speed.** Over a step that goes on, the speed is the time between the
captures of the content at either end of the step, divided by the time
between the two output samples leaving (`World.speed`). A speed of one plays
the source at the pitch and tempo at which it was captured; a speed `v`
shifts the pitch by `1200·log₂ v` cents. The speed is one less how fast the
latency changes (`speed_eq`): changing latency by `ΔL` within a time `T`
needs speeds that differ from one by `ΔL/T` on average.

**Roughness,** the measure of rate distortion: at each output sample, the
square of how much the speed changes there, divided by how long it takes to
change (`World.roughnessCost`). Over a playback that goes on, the sum is the
integral of the square of the speed's derivative. Section 6 says where this
comes from.

**Missed samples** (`missedAt`): one kind of event, counted in samples.

- An output sample that plays anything but the source counts one.
- An output sample that plays the source counts the frames that its content
  skips or plays again since the last output sample that played the source,
  beyond those that the output samples in between already counted.

So, at a speaker (`missedAt_none`, `missedAt_continues`, `missedAt_skip`,
`missedAt_repeat`, `missedAt_after_gap`, `missedAt_resume`):

| What the speaker does | Missed samples |
|---|---|
| plays on | 0 |
| jumps forward over `J` frames | `J` |
| plays `J` frames again | `J` |
| plays `g` output samples of anything else, then goes on where the content would have been | `g` |
| plays `g` output samples of anything else, then resumes where it stopped | `g` |

A speaker that resumes where it stopped plays everything after a little
later; that costs in synchronisation and latency, not in missed samples.

**Over time.** Each objective is a long-run average over true time
(`longRun`): what it accrued before true time `T`, per second, in the limit
superior as `T` grows. A cost of a frame accrues at the frame's capture,
times the time until the next capture, so that the sum is an integral over
time (`World.accruedFrames`); a cost of an output sample accrues when it
leaves, averaged over the speakers (`World.accruedOutputs`). In units:
synchronisation and tracking in square seconds, latency in seconds,
roughness in one over square seconds, missed samples per second.

**Together.** The cost of a run is the long-run average of the weighted sum
of what the five objectives accrue (`World.cost`), with weights for
synchronisation, latency, tracking, roughness and missed samples
(`Weights`). The weights are parameters: a solution is designed for
weights, and statements about solutions say for which. The two modes are two
kinds of weights: low-latency mode has a zero weight for tracking, lip-sync
mode a zero weight for latency. How the objectives combine may be revisited
once the limits and the solutions are known.

The cost of a solution in a world is the cost of its worst run there
(`Solution.cost`). When the world is random, a world `world ω` with `ω`
drawn from a probability measure `P`, the cost of a solution is its expected
cost (`Solution.expectedCost`).

## 6. Rate distortion: where the measure comes from

The earlier work that this project started from charges the **warp**, the
fractional amount by which a receiver's resampler plays faster or slower
than its nominal rate, with the integral of the square of the warp's
derivative, `∫ u̇(t)² dt`, the `Ḣ¹` seminorm. It charges the derivative and
not the warp itself on purpose:
fast changes of pitch are heard as chirps, while a slowly varying offset of
pitch is not heard. Its bound on the warp, half a percent, is the
resampler's limit and not a cost.

Here the speed is that of the content against its capture, in true time:
the speed as heard. Its steady value is one; the clocks' drift does not
appear in it, only in what a solution does to keep it at one. The earlier
warp is the resampler's rate against its own device, whose steady value is
the drift. The two derivatives differ only by how fast the clocks' own rates
change, so the roughness here is the earlier warp cost, measured on what is
heard.

Open, for discussion:

1. The square of the derivative weighs a modulation of the speed by the
   square of its rate. How well listeners detect frequency modulation
   depends on its rate and on what is played; whether this weighting is the
   right shape, or a weighting by modulation rate should replace it, is a
   question for the psychoacoustic literature.
2. The roughness charges how fast the speed changes, not how far it is from
   one. An offset of the speed held for long costs nothing here, though it
   is heard as a shift of pitch once it is large enough, a few cents.
   Whether the size of the shift should also count, as a cost or a bound, is
   open.
3. A jump of the content is not a speed: it counts as missed samples.

## 7. Models of the world (`Models`)

A model of the world says which worlds can happen and, when the world is
random, how likely each is. Statements hold under a model, and the same
solution can do differently under different models. Each model is a file of
its own in `lean/Unisono/Spec/Models`.

The first model, `Bounded`, has no chance in it. It bounds how far each
host's clock and each device may run from their nominal rates, how wrong a
device's report may be, how long before its first output sample a device
asks for a block, and the least and the most time a message takes on each
way between two hosts (`World.WithinBounds`). A statement under it holds for
every world within the bounds: the worst case. A random world can be
required to be within bounds almost surely (`AlmostSurelyWithin`).

Models with laws of chance, for the delays, the losses and outages of the
network, and the wandering of the clocks, come with the statements that
need them. Some will need mathematics that Mathlib does not have yet; that
is formalised as a library of its own, apart from the specification and
from any solution.

## 8. Choices made here, to review

1. One nominal rate for all devices.
2. Content between two frames was captured between their captures in
   proportion, and playing content at a position needs the two frames
   around it. A solution that reproduces content from more frames waits for
   more.
3. Whether a message arrives, and when, depends on the two hosts, when it is
   sent and how many messages went before it on the same way, not on its
   size or on the network's load. The network's capacity is a budget of
   messages and frames a second for each way between two hosts.
4. A host answers a device's request at the moment of the request; the time
   it takes to compute is not modelled.
5. A host reads its clock exactly at its events. A device's reports may be
   wrong; by how much is part of a model.
6. Playback goes on while the content advances by more than nothing and less
   than two frames per output sample. Playing faster than double speed is
   counted as skipping.
7. Synchronisation compares the times at which speakers play the same frame,
   not their latencies at the same moment. The two agree while latency
   changes slowly.
8. Latency counts linearly and tracking quadratically, as in the earlier work.
9. A frame missed at a speaker does not count in that speaker's
   synchronisation, latency or tracking; it counts as missed samples.
10. When a solution has several runs in a world, its cost there is the
    worst. That a solution has exactly one run, when every message takes
    some time, is not yet proved; admissibility asks for one.
11. The hosts are the sender's and the speakers'. A host that serves as a
    reference clock and nothing else is outside the scope.
