# The model

This page states the problem unisono solves: the clocks, what can be measured
about them, the stream, the disturbances and the objective. Each statement is
a definition, an assumption about the world, or a claim. An assumption names
the quantity that monitors it at run time. A claim is followed by the name of
its statement in `lean/`, or by *not stated in Lean*. Symbols are defined where
they are used, and all times are in seconds.

## 1. Clocks

A host reads time from its **raw clock**, an oscillator that no time service
corrects. Write $C_h(t)$ for the reading of host $h$'s raw clock at true time
$t$. True time is never observed; only readings are.

The **fractional frequency** of host $h$ is $y_h(t) = \dot C_h(t) - 1$, the
amount by which its clock runs fast.

**Assumption (oscillators).** $|y_h| \le y_{\max}$, and over any stretch of
time $T$ that an estimate remembers, a clock departs from a straight line by at
most $b(T)$. A frequency that changes by at most $a$ per second gives
$b(T) = a T^2 / 8$. The simulations draw the frequency from a random walk, which
obeys such a bound only with high probability. *Monitor:* the rate at which the
fitted line of section 6.3 changes its slope.

There is one sender $S$ and there are receivers $r = 1, \dots, N$. The
**offset** of receiver $r$ is $x_r(t) = C_r(t) - C_S(t)$, and its **relative
frequency** is $\dot x_r = y_r - y_S$. Receivers on one host share its clock
and one offset.

An audio device counts frames. Write $P_d(t)$ for the count of device $d$ at
true time $t$, and $f_d$ for its nominal rate in frames per second. A device's
counter is a clock like any other, with its own fractional frequency.

**What true time is not.** Every measurement below is a set of readings, each
of one clock at one event. Renaming the instants, so that every clock and
every event is moved by the same increasing map of true time, changes none of
them. Nothing in unisono can therefore depend on true time, and no host's
clock is privileged by nature. The sender's raw clock is the time base by
convention. *Not stated in Lean.*

## 2. Measurements

### 2.1 Two clocks of one host

Reading clock $A$, then clock $B$, then clock $A$ again gives the difference of
the two to within half the time between the two readings of $A$. This relates
the raw clock to the clocks in which a kernel or an audio system reports time.
The error has either sign.

### 2.2 A packet

The sender stamps a packet with the reading $t^{\mathrm{tx}}$ of its clock at
departure, and the receiver with the reading $t^{\mathrm{rx}}$ of its own clock
at arrival. Define the packet's **delay** $d$ as its transit time read on the
sender's clock. Then, exactly,

$$z \;=\; t^{\mathrm{rx}} - t^{\mathrm{tx}} \;=\; x_r(\text{arrival}) + d .$$

**Assumption (delay).** $d = \delta_r + \eta$, where $\delta_r$ is the smallest
delay of the path for packets of this size, and $\eta \ge 0$ is the excess. A
packet is delayed, never early. Over the time $T$ that the estimate remembers,
there is a packet with $\eta \le \epsilon$ in the first half and one in the
second. Nothing is assumed of the other packets: they may wait in a queue, or
through a pause of the link. *Monitor:* how far the lowest packets of
successive windows lie above the fitted line.

**Assumption (stamps).** A stamp errs toward delay: the stamp of a departure is
not after the departure, and the stamp of an arrival is not before the arrival.
The kernel's stamps are so by construction. Where the program has to stamp a
packet itself, it reads the clock before sending and after receiving. The
conversion of section 2.1 adds an error of either sign, of tens of nanoseconds.
*Monitor:* samples that lower the fitted line by more than a set amount.

A sequence of such packets shows $x_r + \delta_r$ along its lower edge. One
direction alone therefore determines the relative frequency, and the offset up
to the constant $\delta_r$.

The smallest delay grows with the size of a packet: each link that stores a
packet before forwarding it adds the time the packet takes on the wire, 120 µs
for 1500 bytes at 100 Mbit/s. On a wireless link it also moves with the
transmission rate.

### 2.3 An exchange in both directions

A packet leaves the sender at $t_1$ (sender's clock) and arrives at $t_2$
(receiver's clock). A packet leaves the receiver at $t_3$ and arrives at $t_4$.
Let $d^{\to}$ and $d^{\leftarrow}$ be the two delays, both read on the sender's
clock, and let $x^{(2)}$ and $x^{(3)}$ be the receiver's offset at the moments
of $t_2$ and $t_3$. Then, exactly,

$$\frac{(t_2 - t_1) - (t_4 - t_3)}{2} \;=\; \frac{x^{(2)} + x^{(3)}}{2} + \frac{d^{\to} - d^{\leftarrow}}{2},
\qquad
(t_4 - t_1) - (t_3 - t_2) \;=\; d^{\to} + d^{\leftarrow} - \bigl(x^{(3)} - x^{(2)}\bigr).$$

*Lean:* `Unisono.Model.Exchange.offset_identity`, `round_trip_identity`.

The first quantity is the offset with an error of half the difference of the
delays. Half the difference of the two *smallest* delays,
$(\delta^{\to} - \delta^{\leftarrow})/2$, is a constant that no exchange
reveals. The rest is at most half the amount by which the two delays together
exceed the two smallest delays together.
*Lean:* `Unisono.Model.Exchange.error_bound`.

In the second quantity the last term is the change of the offset while the
receiver held the exchange: the relative frequency times that time. It is
removed with the fitted slope.

### 2.4 A device

An audio system reports pairs $(p, T)$: the device's counter read $p$ when the
host's clock read $T$.

**Assumption (device reports).** The error $\nu$ of a report has either sign
and is bounded, $|\nu| \le \nu_{\max}$, which requires the audio system to take
the two numbers of a pair together. Sound leaves a playback device a constant
time $D_d$ after its counter passes a frame, and entered a capture device a
constant time before. *Monitor:* the residuals of the reports against the
device's fitted line.

### 2.5 What cannot be observed

Three things stay outside every measurement above, and they bound what
software can promise:

- true time (section 1);
- for each receiver, half the difference of the smallest delays in the two
  directions, for packets of equal size;
- for each device, its constant delay $D_d$.

## 3. The stream

The sender's capture device counts frames from the start of a **timeline**; the
count is the frame's **index** $n$. The **capture time** $\tau(n)$ is the
reading of the sender's clock when the device's counter passed $n$, taken from
the sender's fitted line for its device (section 2.4).

The **level** $\ell(n)$ is the latency that every receiver holds for frame $n$.
The sender announces it ahead of the frames it applies to, so that all
receivers move it together. Frame $n$ is to leave each receiver's device when
the sender's clock reads $\tau(n) + \ell(n)$.

For receiver $r$, let $t^{\mathrm{out}}_r(n)$ be the true time at which frame
$n$ leaves its device. Its **timing error** is

$$e_r(n) \;=\; C_S\bigl(t^{\mathrm{out}}_r(n)\bigr) - \bigl(\tau(n) + \ell(n)\bigr),$$

positive when the frame is late. The **synchronization error** between two
receivers is $e_r(n) - e_{r'}(n)$, and the **latency** of receiver $r$ is
$\ell(n) + e_r(n)$, plus what section 6.1 says the sender adds.

Frame $n$ arrives at receiver $r$ with a **delivery delay** $D_r(n)$ after its
capture: everything from capture to the frame lying in the receiver's buffer.
The receiver has to hand a frame to its device a **lead** $\Lambda_r$ before it
is due: a cycle of the device, what the device buffers, and the resampler's
lookahead. The **margin** is
$m_r(n) = \ell(n) + e_r(n) - D_r(n) - \Lambda_r$. A frame with negative margin
is **missed**: it is due before it is there, and the receiver conceals it. A
**gap** is a run of missed frames longer than concealment covers.

What the frame **needs** at receiver $r$ is the level at which it is just
there in time: $D_r(n) + \Lambda_r - e_r(n)$. A receiver misses the frame
exactly when the level is below that, and the group of receivers misses it,
meaning that at least one receiver does, exactly when the level is below the
largest need over the receivers.
*Lean:* `Unisono.Model.Stream.margin_neg_iff`, `group_misses_iff`.

## 4. Disturbances

**Assumption (delivery delay).** $D_r = B_r + \varepsilon_r + \Pi_r$:

- a **baseline** $B_r$ that moves slowly;
- a **deviation** $\varepsilon_r$, stationary with light tails, of
  sub-millisecond size on wired links;
- **pauses** $\Pi_r$: episodes during which nothing arrives. An episode of
  length $H$ delays the audio captured at its start by $H$ and what follows by
  less, down to zero at its end. Episodes form a marked point process with a
  rate and a law of lengths, both measured; they cluster, and they coincide
  across receivers far more often than independence would give.

Packets are also lost, in bursts.

*Monitors:* the estimated baseline; the histogram of deviations; the record of
pause lengths and of the times between pauses; the record of loss bursts.

A stationary delay adds no accumulating noise to a buffer: a delay that rises
by some amount takes that amount from the margin once, and gives it back when
it falls.

## 5. The objective

The cost per second, for a stream with $N$ receivers, is

$$w_{\mathrm{lat}}\,\bar\ell
\;+\; w_{\mathrm{tgt}}\,(\bar\ell - L_0)^2
\;+\; w_{\mathrm{gap}}\cdot(\text{gaps of the group per second})
\;+\; w_{\mathrm{miss}}\cdot(\text{fraction of frames the group misses})
\;+\; \sum_{r}\Bigl[\,w_{\mathrm{sync}}\,e_r^2
\;+\; w_{\mathrm{rough}}\,\dot u_r^2\Bigr],$$

subject to $|u_r| \le u_{\max}$. Here $\bar\ell$ is the level, $L_0$ a target
latency, $e_r$ the timing error of receiver $r$ against the common schedule,
and $u_r$ the amount by which receiver $r$ plays fast (section 6.4).

The timing errors are counted against the schedule, which no receiver has to
ask another about. Their squares add up to the squared distances of the
errors from their mean over the receivers, which is what is heard as
receivers being out of step with each other, plus the squared mean once for
each receiver, which is all of them being early or late together.
*Lean:* `Unisono.Model.Stream.sum_sq_errors`.

Gaps are counted on the group. The group misses a frame when at least one
receiver has nothing to play for it, and a gap of the group is a run of such
frames: receivers that drop out at the same moment make one gap, which is
what a listener hears. The two other ways of counting are both wrong. A mean
over the receivers lets nine receivers on good links make the gaps of a
tenth count a tenth as much, so the level falls and that receiver drops out
more, though whoever listens to it hears the same as before. A sum over the
receivers counts a gap that all of them share $N$ times, so the level rises
with the number of receivers for a cause that the level of a larger group
does nothing more against.

The weights, $L_0$ and $u_{\max}$ are parameters of a stream; no value of them
is built in. A large $w_{\mathrm{tgt}}$ holds the latency at $L_0$, which suits
audio that accompanies video. With $w_{\mathrm{tgt}} = 0$ the latency follows
the link. A gap is priced by its occurrence, since a thousand gaps of a
millisecond are not one second of silence; missed frames are priced as well,
or one endless gap would be the cheapest way to play.

## 6. What follows

### 6.1 The parts of the timing error

Receiver $r$ turns the due time $\tau(n) + \ell(n)$, which is on the sender's
clock, into its own clock with its estimate of the offset, and then into a
position of its device with its fitted line for the device. Its timing error is
the sum of:

- the error of its estimate of $x_r + \delta^{\to}_r$ (section 6.3);
- the error of its estimate of the constant $\delta^{\to}_r$, which contains
  half the difference of the smallest delays, $\tfrac12(\delta^{\to}_r -
  \delta^{\leftarrow}_r)$, that nothing reveals;
- the error of its device's fitted line, and of the conversion between the raw
  clock and the clock the audio system reports in;
- its device's delay $D_d$, less the delay the receiver assumes for it;
- the delay of its resampler, which is known, less what it compensates;
- the error of its regulator (section 6.4).

The sender adds two things to every receiver alike: the error of its own
device's line, and its capture device's delay. They are part of the true
latency and of the margin, and no part of the synchronization error.

The delivery delay of section 4 is not in the list: when the schedule comes
from clocks, jitter and pauses of the network do not move the playback rate.
They act on the margin, and the level answers them (section 6.5). This rests
on the estimate of section 6.3 being unmoved by delayed packets.
*Not stated in Lean.*

### 6.2 The sender's clock and synchronization

Suppose the sender's clock is replaced by $a + (1+b)\,C_S$, for constants $a$
and $b$. Every stamp of the sender changes. For a receiver's fitted line and a
fixed set of the samples it keeps, the reading of the receiver's clock that the
line assigns to an event does not change.

*Lean:* `Unisono.Model.LineFit.schedule_invariant` for the least-squares line;
for the line of section 6.3, `Unisono.Model.SupportLine.under_add` shows that a
line under the samples stays under them. That the two receivers keep the same
samples before and after, that the path constant and the device lines follow,
and the statement for the difference $e_r - e_{r'}$ itself are *not stated in
Lean*.

A *change* of the sender's frequency does reach each receiver's line: a line
through a curve departs from it by the $b(T)$ of section 1. Two receivers that
remember the same stretch of time $T$ meet the same departure, and it cancels
in their difference. The memory is therefore one number for the stream,
announced like the level, and not chosen by each receiver.

### 6.3 The estimator

For one host, the quantity to track is $\theta(t) = x_r(t) + \delta^{\to}_r$,
seen through the values $z$ of section 2.2. Every sample lies on or above it.

**Selection.** Packets are grouped into windows by index. From each window the
packet that lies lowest against the current line is kept. This thins the
samples; it is not what makes the estimate right.

Packets can overtake each other, so a sample of an earlier window can arrive
when its window has ended. It is left out, on one condition: its time is not
later than the latest sample taken in, and not earlier by more than the memory
$T$. A packet that was overtaken meets that condition. A sample of an earlier
window that does not meet it cannot come from such a packet: the sender has
started again and numbers its windows anew, and the sample begins a window. A
rule that left out every sample of an earlier window would be simpler and
wrong: after a sender has started again with lower indices, the estimate would
stay that of the run before until the new run had gone as far.

**Fit.** Kept samples older than the memory $T$ are forgotten. The estimate is
the line that lies on or under every kept sample and is highest at the middle
of the time they cover. It passes through two kept samples, one on each side of
the middle.

Claims, for kept samples at times $t_j$ with values $z_j$, and $c$ the middle:

- *The line through two samples on either side of $c$ that lies under all
  samples is the highest at $c$ of all lines under the samples.*
  *Lean:* `Unisono.Model.SupportLine.highest`.
- *In what sense it is the best.* A sample is never below the true relation,
  so the lines that the samples allow as the true relation are the lines
  under the samples. The estimate is one of them, and its value at $c$ is the
  largest of theirs (`estimate_isGreatest`): it is the least estimate that is
  never below a relation the samples allow. And when $c$ is the mean of the
  times of the samples, the samples lie above the estimate by no more, added
  up, than above any other line under them (`excess_le`); that sum is what
  the likelihood of a line depends on when the excesses of the samples are
  independent and exponential, whatever their rate, so the estimate is then
  the most likely line. The code takes $c$ in the middle of the time that the
  kept samples cover, which is the mean of their times when they are evenly
  spread.
- *Its error at $c$.* If every sample is on or above the true relation, the
  true relation stays within $b$ of a line, and one sample at or before $c$ and
  one at or after it are within $\epsilon$ of the true relation, then the
  estimate at $c$ is at most $b$ below that line and at most $\epsilon + b$
  above it. Nothing is asked of the other samples.
  *Lean:* `Unisono.Model.SupportLine.error_at_centre`.
- *Its error after the newest sample*, where the schedule needs it, is larger
  by the lever of the extrapolation: by $\epsilon + 2b$ for every half of the
  memory that the time lies beyond $c$, when the two samples near the true
  relation are at the ends. *Lean:* `Unisono.Model.SupportLine.error_ahead`.
- *The past is forgotten.* After a time $T$, and after as many windows as there
  are places for samples, nothing that was kept before remains.
  *Not stated in Lean.*

About the code that computes it (`unisono_core::relation`), over the integers
and without rounding, all in `Unisono.Relation`: `side_spec` (the test of which
side of a line a sample lies on), `is_under_spec` (whether a line lies under
all kept samples), `put_spec`, `drop_oldest_spec` and `forget_before_spec`
(keeping and forgetting samples), `bridge_spec` (the two samples the line is
drawn through are kept samples around the middle), and `fit_spec`: the fit
ends for every state, changes nothing but the line, and a line it newly stores
passes through a kept sample and has no kept sample below it. The statements
hold for times and values within an eighth of the 64-bit range, which is 36
years in nanoseconds.

For every state of the estimator, in range or not, and every packet, taking
in a packet and ending a window return: `observe_total`, `end_window_total`.
Nothing in the estimator can fail or run forever.

The estimator also takes a stream in again from any state. `observe_spec`
says what a sample does: one that can come from an overtaken packet leaves the
estimator exactly as it is, and every other one is taken in, after which the
estimator holds that sample's window. A sample later than every sample taken
in is always taken in (`observe_later`), and so is every sample of the window
held or a later one (`observe_in_order`). A sample that is left out is at most
$T$ earlier than the latest one taken in, and leaving it out changes nothing.
So whatever the estimator holds, of a stream whose time goes on it leaves out
at most the samples of the first $T$, and takes in all that follow.
`crates/unisono-core/tests/restarts.rs` runs a receiver through each way a
sender can start again: the same timeline number with the index back at the
start, on a clock that began anew, on the same clock and on a clock that reads
a little less; a later timeline on the same clock and on another; and another
sender with the same identifiers.

Not stated in Lean: that the fit always finds a line when there are two kept
samples, which needs the hull to be built correctly and is covered by tests;
and what the kept samples are after a packet, in terms of the packets before.

**Limits of the slope.** A slope beyond what $y_{\max}$ allows for two
oscillators means an assumption has failed, as when the first sample of all
was a delayed one. The estimate then takes the nearest allowed slope and the
highest line of that slope under the samples. *Not stated in Lean.*

**What breaks it.** A sample that is too low, which the stamp assumption
excludes, lowers the line by its full error until it is forgotten. A smallest
delay that rises is followed only after the time $T$.

**Reference.** A Kalman filter for a random-walk frequency, fed the same kept
samples, is run beside the estimate in simulation. It is the best estimator
when the error of a sample has either sign, which here it has not.

**The constant.** The same estimator runs on the packets of the other
direction, with the same memory, and gives $-x_r + \delta^{\leftarrow}_r$.
Half the difference of the two estimates is the offset, up to the constant of
section 2.5; half their sum is the smallest delay of the path, which monitors
it. The packets used for this are of one size in both directions.

In the code the packets of the other direction are the receiver's reports,
padded to the size of an audio packet, and the sender's answers carry their
arrival times (`docs/protocol.md`). The receiver does not fit a second line
to them. An answer says when its report left on the receiver's clock and
when it arrived on the sender's; the line from audio packets, evaluated at
that arrival, says the receiver's clock minus the sender's plus the
smallest delay from the sender. In the sum of the two the clocks cancel, and
what is left is the smallest delay from the sender plus the delay of that
report back: a time there and back that depends on neither clock. The delay
of a path is a constant, so the memory is long: of each window of eight
seconds the answer with the shortest time there and back is kept, for eight
windows, and the shortest of those, halved, is the delay of the path from the
sender (`unisono_core::answers`). The answers themselves are kept, not their
times, and the times are worked out with the line as it is when the delay is
taken: a time worked out with an early line, which can be off by
microseconds, would otherwise stay the shortest for a minute. A clock that
changes does not touch what is kept, and neither does a new timeline. Taking
in an answer returns for every state and changes nothing about the timeline
or the frames held (`Unisono.Receiver.echo_spec`, with `Unisono.Answers`).

Reports are sent twenty a second for the first five seconds and five a
second after. In simulation (`crates/unisono-sim/tests/timing.rs`), with five
reports a second, receivers that find their delay this way stay within half
a microsecond of the schedule on the calm wired link, within four on the
busy one and within fifty on the wireless one (measured: 0.3, 3 and 30);
told the true delay they stay within a quarter, one and a half and 25. With
twenty reports a second the figures are 0.2, 2 and 16 once settled, and with
one a second 0.5, 11 and 60. Five reports a second, each as large as an
audio packet, are a fortieth of the packets of the stream. The estimate errs
high, by the queueing of the best report in the memory, which is why more
reports help. A
path that is slower one way shifts the receiver by half the difference, as
section 2.5 says, and a test shows it.

**Devices.** The reports of a device, each a count of frames and the time
that belongs to it, have errors of either sign, so a device's line is fitted
by least squares. The core (`unisono_core::device::Device<W>`) fits the line
to the last `min(W, 4096)` reports, without weights, in exact sums of 128-bit
integers taken relative to the newest report and to the nominal rate.

A device's timing can also make a step: it leaves frames out, or stands still
for a cycle, and from then on every frame leaves it later than its count says
by the same amount. A line fitted across a step is wrong on both sides of it
for as long as reports from before the step are kept. So a report is first
held against the report before it. If the time between the two is what the
frames between them take at the nominal rate, within half of that, the report
is kept. If not, it is set aside for one report:

- the next report lies where the one set aside puts it: the timing made a
  step. The kept reports are moved by the step and the two reports are kept.
  The line keeps the rate it had, which a step does not change, and goes on
  through the new reports;
- the next report lies where the kept reports put it: the one set aside was
  wrong, and is dropped;
- neither: the line starts anew at that report, as it does when a count of
  frames goes back.

The size of the step is the mean of how far the two reports lie from the
line, so it is known as well as two reports tell it; the line is as good as
before the step once the kept reports are all from after it. A device that
leaves out a cycle is off by the whole time of a cycle, and two reports that
are each wrong by less than a quarter of it are never apart by more than
half, so the rule takes no report for a step as long as reports are that
good. In simulation, with reports off by up to 20 microseconds and a device
that stands still for one cycle of 5.3 ms, the receiver plays within 17
microseconds from the third cycle on, and within the 12 of undisturbed
playback 64 cycles later; without the rule it is 5.3 ms off at the third
cycle.

*Lean:*
- `Unisono.Model.LineFit`: `cost_le` (the line computed from the weighted sums
  has the smallest weighted sum of squared residuals), `moment_shift`,
  `moment_scale`, `moment_insert` (the sums can be kept as samples come and
  age), `error_bound` (a bound for errors that are bounded).
- `Unisono.Device`: `when_spec` (for any `W`, no sum or product wraps, and
  the result is the stated function of the kept reports), and
  `beyondZ_eq_floor_lineFit` (when the kept reports are of at least two
  positions, that function is the nominal time plus the least-squares line of
  `Unisono.Model.LineFit` through the departures from it, rounded down).
- `Unisono.Device.observe_spec`: for every state of the device and every
  report, the report is either kept, as the newest of the kept reports with
  the counts within what the device can hold, or it is set aside with
  everything else as it was, and that only when nothing was set aside before.
  So of any two reports in a row the second is kept
  (`observe_after_aside`): whatever a device holds, its line follows the
  reports again from the second one on.

### 6.4 The regulator

The receiver's resampler reads the stream at a pace of its own. The schedule
of section 3, as the receiver estimates it, says where it should be reading
and how fast. The regulator chooses the pace, once for each cycle of the
device, from what the receiver knows before the cycle. This section states
that choice as a problem, solves it, and says what is proved.

**The problem.** Before a cycle the receiver knows two numbers, both in
frames:

- $E$, the distance by which the position it reads at is behind the
  schedule;
- $v$, by how much the cycle would read further than the schedule advances
  over it, if it kept the pace of the cycle before.

It chooses $w$, the change of its pace: the cycle then reads $v + w$ further
than the schedule advances. Between two cycles the receiver's estimate of the
schedule is revised, in position by $\xi_1$ frames and in pace by $-\xi_2$
frames a cycle. One cycle therefore takes the state $(E, v)$ to

$$E' = E - v - w + \xi_1, \qquad v' = v + w + \xi_2 .$$

A cycle costs $\rho\,E^2 + w^2$, with one number $\rho > 0$. The first term is
the timing error of section 5, the second the change of the pace, which is
what is heard as a change of pitch. With the weights of section 5 and cycles
of length $h$, $\rho = a^4$ for $a = \kappa h$ and
$\kappa = (w_{\mathrm{sync}} / w_{\mathrm{rough}})^{1/4}$, the regulator's gain
per second: a pace that is constant within a cycle changes only between the
cycles, and the sum of its squared changes, divided by $h$, is the integral of
$\dot u^2$ for the smoothest pace through the same values. The timing error
is charged where it is measured, at the start of each cycle.

The receiver may choose each $w$ from everything it has seen before that
cycle, in any way. The problem is to make the cost of all cycles smallest:
their sum when the schedule is not revised, and the mean of their sum when it
is.

**The solution.** Let $d$, strictly between 0 and 1, be the smaller root of

$$d + \frac1d \;=\; \frac{a^2 + \sqrt{a^4 + 16}}{2},
\qquad\text{so that}\qquad a^2\,d\,(1 + d^2) = (1 - d^2)^2 ,$$

and $g = 1 - d^2$. The law is

$$w \;=\; a^2 d\,E \;-\; g\,v,
\qquad\text{that is, the cycle reads}\quad d^2\,v + a^2 d\,E
\quad\text{further than the schedule advances.}$$

Its cost of all cycles from the state $(E, v)$, when the schedule is not
revised, is the value

$$V(E, v) \;=\; g\,\Bigl(v - \frac{g}{2 - g}\,E\Bigr)^{2} + \frac{a^4}{g}\,E^2 .$$

All of the following is proved in Lean, for the recursion over the real
numbers, in `Unisono.Model.Regulation` and `Unisono.Model.RegulationRandom`.
The statements there have $g$ as the parameter; the gain on the distance is
then $g^2/(2-g)$ and the weight is $g^4 / ((2-g)^2 (1-g))$, which are $a^2 d$
and $a^4$ for the $g$ above (`gainE_gainFor`, `weight_gainFor`), and no other
$g$ between 0 and 1 belongs to the weight $a^4$ (`gain_unique`).

- *One identity carries everything* (`cost_add_value`): for every state and
  every $w$, the cost of the cycle plus the value of the state after it is
  the value of the state before it plus $(w - w^\ast)^2 / (1 - g)$, where
  $w^\ast$ is what the law chooses.
- *A schedule that is not revised.* The costs of all cycles under the law add
  up to the value (`total_cost_law`), and for every sequence of changes of
  the pace whatever, chosen with or without knowledge of the future, the
  costs add up to at least the value if they add up at all
  (`total_cost_ge`). So the law is the best there is, from every state.
- *A schedule that is revised.* Let each revision have the mean zero given
  everything the receiver has seen before it, and a finite mean square;
  nothing else is asked of the revisions, which need not be independent, of
  one law, or Gaussian. For every way of choosing the pace from what has been
  seen, and every number of cycles, the mean cost of the cycles plus the mean
  value of the state after them is the mean value at the start, plus the mean
  values of the revisions, plus the mean of $(w - w^\ast)^2/(1-g)$ over the
  cycles (`mean_cost_sum`). The first two parts are the same for every way of
  playing; the law makes the third zero (`mean_cost_law_le`). What any other
  way of playing loses against the law is exactly that third part.
- *In the long run.* Under the law the mean value of the state stays bounded
  when the mean values of the revisions are (`mean_value_law_le`), so over
  many cycles its mean cost of a cycle is the mean value of a revision. No
  other way of playing does better: when the mean value of every revision is
  at least $s$ and the mean squared revisions of the position are bounded,
  the mean cost of a cycle does not stay below $s$, for any way of choosing
  the pace from what has been seen (`mean_cost_rate`). A way of playing can
  cost less over some cycles only by leaving a state of larger mean value,
  and such a state is paid for within two cycles (`mean_value_le_costs`).
- *The true schedule.* The receiver follows its estimate, and $E$ is the
  distance to the estimate. When the estimate of a quantity is its mean given
  what the receiver has seen, the mean squared distance of the receiver's
  position from the true quantity is the mean squared distance from the
  estimate plus the mean squared error of the estimate
  (`mean_square_split`), and the second part is the same for every way of
  playing. A revision of such an estimate has the mean zero given what was
  seen before (`unforeseen_revision`). So with estimates of that kind, the
  law that is best against the estimate is best against the truth.
- *How fast it settles.* Under the law every cycle multiplies the value by
  exactly $d^2$ (`value_step`, `value_step_gainFor`). From rest, as after a
  start or a jump, the squared distance after $k$ cycles is at most
  $(2 - g)\,d^{2k}$ times the squared distance at the start
  (`distance_from_rest`).
- *A pace that is wrong.* When the schedule advances by $\delta$ frames more
  in each cycle than the receiver is told, the state moves as without the
  error around the point where the distance is $(2 - g)\,\delta / g$
  (`next_shift`), so that is where the distance tends.
- *The limit.* A cycle whose pace is held at the limit $L$ starts at least
  $(2 - g) L / g$ from the schedule and ends $L$ nearer (`at_limit`), so the
  limit holds for no more cycles in a row than the distance holds limits.

For short cycles, $g \approx \sqrt2\,a$ and $a^2 d \approx a^2$: the law
becomes $\dot{\tilde u} = \kappa^2 e - \sqrt2\,\kappa\,\tilde u$, with damping
$1/\sqrt2$, which is the best law of the problem in continuous time. For the
cycles that a device has, the two differ by terms of the order of $a$, and
only the law above is the best.

**What the result assumes.** That the revisions cannot be foreseen is an
assumption about the estimates and about the world. For the revisions of the
position it holds when the schedule that the regulator follows is the mean of
the true schedule given what the receiver has seen (`unforeseen_revision`).
For the revisions of the pace it holds when, besides, the pace of the true
schedule is expected to stay as it is, as for clocks whose frequency wanders
without a direction; that step is *not stated in Lean*. The estimates of
section 6.3 are not derived as such means: the line under the samples lies
above the true relation by up to the bound given there, and the device's line
is a least-squares fit to its last reports. What that costs is *not stated
in Lean* either. *Monitor:* the correlation between successive revisions of
the schedule's position and pace, which is zero for revisions that cannot be
foreseen.

**The level's slope.** The sender announces the level and its slope with the
frames they apply to, so a change of the slope is no revision: the receiver
knows it before it plays the frames. The regulator carries the pace of the
cycle before over to the new slope and applies the law to what remains. A
moving level is therefore followed at once, by all receivers alike, and the
change of pace at the start and at the end of a move belongs to the cost of
moving the level (section 6.5), not to the regulator.

**The limit of the pace.** The bound $u_{\max}$ is on the whole pace, the
scheduled part included: a level that moves and a regulator that corrects
share it. The step from one output frame to the next is limited, and the pace
that is kept for the next cycle is that of the step taken. A change of the
playback rate is heard as a change of pitch when it is large and fast enough;
published thresholds for pure tones are one to three parts per thousand. In
steady state the rate moves by far less: the line of section 6.3 changes by
fractions of a microsecond per window. A distance beyond a set number of
frames is not played away: the position jumps to the schedule.

**The code** (`unisono_core::player`) keeps the position and the pace of the
cycle before, and computes $v$, the gains $d^2$ and $a^2 d$ from the gain per
second and the length of the cycle, and the step, in whole numbers. The
square roots are taken exactly, rounded down (`unisono_core::fixed::root`),
and $\sqrt{y^2 - 4}$ for $y = d + 1/d$ is taken as $\sqrt{a^2 y}$, which is
the same number and loses nothing for a small $a$; a test holds the gains
against the formulas above to eight decimal places for cycles from a tenth of
a millisecond to a quarter of a second. The gain of a cycle is held at one or
below.

About the code, in Lean: planning a cycle returns for every state, schedule
and reading of the clock, and the step of its plan is within the limit of the
pace, however far the schedule advances over the cycle and whatever the state
of the regulator (`Unisono.Player.cycle_spec`). The limit counts as three in
a thousand when it is set higher, so every step is one that the resampler
takes (`cycle_step_small`). Planning a cycle changes nothing of a receiver
but its regulator (`Unisono.Receiver.cycle_spec`). *Not yet stated in Lean:*
how far the computation in whole numbers is from the recursion in real
numbers, and that after the limit has let go it does not take hold again.

In simulation (`crates/unisono-sim/tests/timing.rs`), with the cycle lengths
taken from a device that is 120 parts per million off its nominal rate, the
remaining error is as the formula above says when the receiver ignores that
rate: $(2 - g)/g$ cycles at 120 parts per million, which is 42 microseconds
for a gain of 4 per second and cycles of 5.3 ms.

**Large errors.** At a start and after a pause the error can be far larger
than the bound on the rate removes quickly. Slewing at the largest rate left,
$u$, takes $|e|/u$, and costs $w_{\mathrm{sync}}\,|e|^3 / (3 u)$ for one
receiver. Jumping costs that receiver one gap, $w_{\mathrm{gap}}$, or nothing
when it is silent. It jumps when the first exceeds the second. An error that
all receivers share is no error of synchronization, and is not answered by each
receiver for itself: the sender moves the level.

In the code the threshold is a setting, in frames, and applies to a distance
either way. A jump back replays nothing: the frames that a receiver has given
to its device are behind its playhead and are not given again, so the receiver
plays silence until the position reaches the playhead.

### 6.5 The level

Receiver $r$ has a frame to play when the level is at least what that frame
needed there: its delay on the way, above the baseline $B_r$, plus the
receiver's lead $\Lambda_r$. The group has every frame when the level is at
least the largest of these over the receivers. Write $R(n)$ for that largest
need of frame $n$. The group misses frame $n$ exactly when $\ell(n) < R(n)$.
Write $\Gamma(\ell)$ for the rate of gaps of the group, and $\Phi(\ell)$ for
the fraction of frames it misses, when the level is held at $\ell$: both are
properties of the one process $R$. A level held at $\ell$ costs

$$J(\ell) \;=\; w_{\mathrm{lat}}\,\ell + w_{\mathrm{tgt}}\,(\ell - L_0)^2
+ w_{\mathrm{gap}}\,\Gamma(\ell) + w_{\mathrm{miss}}\,\Phi(\ell).$$

The level is one number and $J$ is minimized over a line, so no convexity is
needed: pause lengths with several typical values give several local minima.
A minimizer exists when $w_{\mathrm{lat}}$ or $w_{\mathrm{tgt}}$ is positive
and $w_{\mathrm{miss}}$ is.

The sender needs $R$ and not a rate from each receiver: rates do not say
which gaps the receivers share, and the rate of the group lies anywhere
between the largest of the receivers' rates and their sum. So each receiver
reports, for each stretch of frame indices, the largest need of a frame in
it. The stretches are the same for all receivers, because they are counted in
the index. The sender takes the largest over the receivers for each stretch
and has the need of the group.

A receiver measures the need of the first frame of each packet when it takes
the packet in: the level of that frame, less the time by which the frame is
ahead of the receiver's playhead. This counts every part of the delay at
once, the sender's capture cycle and packetizing as well as the path and the
receiver's own device, and it does not depend on the level in force. Reports
carry the needs of the last eleven stretches, so a lost report loses nothing.

**The decision.** The sender does not know the law of the needs. It has the
needs $y_1, \dots, y_m$ of the group in the $m$ stretches it has seen; a
stretch lasts $D$ seconds. Held at the level $\ell$, a stretch that needs $y$,
after a stretch that needed $p$, costs

$$c(\ell;\,p, y) \;=\; w_{\mathrm{gap}}\,[\,p \le \ell < y\,]
\;+\; w_{\mathrm{miss}}\,\min\bigl((y - \ell)^+,\, D\bigr),$$

where $[\cdot]$ is 1 when the condition holds and 0 otherwise, and
$(x)^+$ is $x$ when positive and 0 otherwise. The first term counts a gap
where one starts: the stretch needs more than the level and the stretch
before did not. The second is the time of the frames missed: the frames of a
stretch need less the later they were captured, since they waited less for
the pause that delayed them, so a stretch with $y > \ell$ is late from its
first frame and misses about $\min(y - \ell, D)$ seconds. That count of
missed time is exact for a pause that begins at the start of a stretch, and
too large by less than one stretch for each pause otherwise. The cost per
second of holding $\ell$ is

$$J(\ell) \;=\; w_{\mathrm{lat}}\,\ell + w_{\mathrm{tgt}}\,(\ell - L_0)^2
+ \frac1D\,\bigl(\text{the mean of } c(\ell;\,p, y) \text{ over the next stretch}\bigr),$$

and the sender chooses the level that makes it smallest. What remains to say
is what the next stretch is expected to be.

*One in $m + 1$.* Nothing sets the next stretch apart from those seen: the
law of the $m + 1$ needs is taken to be the same in every order. Then, if no
two needs are equal, the next need is the largest of them with the
probability $1/(m+1)$, whatever the law is.
*Lean:* `Unisono.Model.Level.measure_largest`. After evidence of the length
$T = mD$, a need above all that were seen is therefore expected about once in
$T$. This is why little evidence holds the level high.

*The next stretch.* With the probability $1/(m+1)$ the next stretch needs more
than any that was seen, and starts a gap if its need is above the level.
Otherwise it is one of the stretches seen, each as likely as the others. The
mean of the cost is then

$$\frac{c_1(\ell) + \sum_{k=1}^{m} c(\ell;\,y_{k-1}, y_k)}{m + 1},$$

where $c_1(\ell)$ is the mean cost of a stretch that needs more than all
seen. *Lean:* `Unisono.Model.Level.integral_predictive`. Taking a stretch
that falls between two needs seen as the larger of them does not lower the
cost.

*How much more.* How far above the largest need seen, $M$, the need of such
a stretch lies is not something the needs seen can say. It is taken from a
law fixed beforehand: the need exceeds $x$, for $x \ge M$, with the
probability $\bigl((S + M)/(S + x)\bigr)^2$, with $S = 20$ ms. This is the law
$(1 + x/S)^{-2}$ of a need about which nothing is known, given that it is
above $M$. The scale $S$ is the order of what packets and the cycles of
devices take; the law has no variance, and under it a new largest need lies
above the last by $S + M$ on average, so that pauses have no typical size.
The numbers are about links and devices in general and are not fitted to
anything. *Monitor:* how far each new largest need lay above the one before.

The level so chosen is the best decision under what is stated: the law of
the next stretch above, and the cost $J$. It is found among the needs that
were seen, the level $L_0$ and 256 further levels up to two seconds, which
are closer together near the needs: the mean cost falls only where the level
passes a need that was seen, or smoothly above the largest of them.

On needs drawn with pauses of 10 to 80 ms every 5, 30 or 300 seconds
(`unisono_runtime::level`, in its tests), the level chosen from two or ten
minutes of them cost at most 9% more, over the next half hour, than the best
level held, which only hindsight gives, when a gap is priced as a
millisecond of level held for one or for ten minutes. When a gap is priced
as a millisecond held for a hundred minutes, the level is held higher than
hindsight would: one large need in two minutes, or none, is no ground to
expect few of them, and the cost was up to 1.9 times the best.

**Moving the level.** The level moves to another minimum only when the cost
saved, over the time the evidence covers, exceeds the cost of the move. This
rule is *not derived*: it takes the time that the evidence covers as the time
for which what was seen will go on. The level moves along a line that the
sender announces with the frames, at a slope within the bound of section 6.4,
and every receiver follows it as section 6.4 says. The cost of a move stands
for the two changes of pace, at its start and at its end, that all receivers
make at once.

In the code a receiver takes the level and its slope from the newest packet
for all the frames it plays. A change of the slope therefore reaches the
frames being played before their turn, by as much as the newest packet is
ahead of them: their due times move by the change of the slope times that
time, for all receivers alike, and the regulators take it out again. For a
slope of half a millisecond a second and a level of 20 ms that is 10
microseconds. Keeping the level by index, so that each frame is played at
the level of its own packet, is not built.

*Not stated in Lean:* that the level is the best over all levels and not
only over those tried; the rule for moving; and the count of missed time
from the largest need of a stretch.

## 7. Assumptions at a glance

| Assumption | Section | Used for | Monitor |
|---|---|---|---|
| Oscillators: bounded frequency, bounded departure from a line | 1 | error of the fitted line | change of the fitted slope |
| Delay: never negative; a nearly undelayed packet in each half of the memory | 2.2 | the fitted line | height of window minima above the line |
| Stamps err toward delay | 2.2 | the fitted line | samples that lower the line by much |
| Smallest delays equal in both directions for equal sizes, up to an unknown constant | 2.3, 2.5 | the offset | half-sum of the two fitted lines |
| Device reports: bounded error of either sign, constant delay | 2.4 | device lines | residuals of reports |
| Revisions of the schedule have the mean zero given what the receiver has seen | 6.4 | the regulator's law being the best | correlation between successive revisions |
| Delivery delay: baseline, deviation, pauses | 4 | level | histograms and records of each part |
| The laws of the delivery delay hold over the time the evidence covers | 6.5 | level | short-window against long-window estimates |
| Nothing sets the next stretch apart from those seen | 6.5 | the level | how often a need exceeds all before it, against one in the number seen |
| A stretch that needs more than all seen: the law of how much more | 6.5 | the level | how far each new largest need lay above the one before |
