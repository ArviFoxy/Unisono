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
is due: a cycle of the device and what the device buffers. The **margin** is
$m_r(n) = \ell(n) + e_r(n) - D_r(n) - \Lambda_r$. A frame with negative margin
is **missed**: it is due before it is there, and the receiver conceals it. A
**gap** is a run of missed frames longer than concealment covers.

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
\;+\; \frac{1}{N}\sum_{r}\Bigl[\,w_{\mathrm{sync}}\,e_r^2
\;+\; w_{\mathrm{rough}}\,\dot u_r^2
\;+\; w_{\mathrm{gap}}\cdot(\text{gaps per second})
\;+\; w_{\mathrm{miss}}\cdot(\text{fraction of frames missed})\Bigr],$$

subject to $|u_r| \le u_{\max}$. Here $\bar\ell$ is the level, $L_0$ a target
latency, $e_r$ the timing error of receiver $r$ against the common schedule,
and $u_r$ the amount by which receiver $r$ plays fast (section 6.4).

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

**Fit.** Kept samples older than the memory $T$ are forgotten. The estimate is
the line that lies on or under every kept sample and is highest at the middle
of the time they cover. It passes through two kept samples, one on each side of
the middle.

Claims, for kept samples at times $t_j$ with values $z_j$, and $c$ the middle:

- *The line through two samples on either side of $c$ that lies under all
  samples is the highest at $c$ of all lines under the samples.*
  *Lean:* `Unisono.Model.SupportLine.highest`.
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

**Devices.** The reports of a device have errors of either sign, so its line is
fitted by least squares with weights that fall with age.
*Lean:* `Unisono.Model.LineFit.cost_le` (the line computed from the weighted
sums has the smallest weighted sum of squared residuals), `moment_shift`,
`moment_scale`, `moment_insert` (the sums can be kept as samples come and age),
`error_bound` (a bound for errors that are bounded; it does not shrink as more
samples are averaged, which a bound for random errors would).

### 6.4 The regulator

The receiver's resampler reads the stream at a rate $1 + u$ relative to its
device. The schedule of section 3 asks for a position and a rate $1 + \hat u$.
Both follow from the fitted lines and from the capture times and levels that
the sender announces, so $\hat u$ includes the rate of the sender's device and
the slope of a moving level. Let $e$ be the time by which the resampler is
behind the schedule and $\tilde u = u - \hat u$. Then $\dot e = -\tilde u$, and
the regulator is

$$\dot{\tilde u} \;=\; \kappa^2 e \;-\; \sqrt2\,\kappa\,\tilde u ,
\qquad \kappa = (w_{\mathrm{sync}} / w_{\mathrm{rough}})^{1/4},
\qquad |u| \le u_{\max} .$$

For the terms $w_{\mathrm{sync}}\,e^2 + w_{\mathrm{rough}}\,\dot u^2$ of the
objective, with $e$ observed exactly and $\hat u$ constant, this law is optimal;
it has damping $1/\sqrt2$. *Not stated in Lean.*

The scheduled rate $\hat u$ is fed forward. Under a constant drift the error
therefore goes to zero without an integrator in the loop. An error $d$ in
$\hat u$ leaves an error $\sqrt2\,d/\kappa$.

The bound $u_{\max}$ is on the whole rate, the scheduled part included: a level
that moves and a regulator that corrects share it.

A change of the playback rate is heard as a change of pitch when it is large
and fast enough; published thresholds for pure tones are one to three parts per
thousand. In steady state the rate moves by far less: the line of section 6.3
changes by fractions of a microsecond per window.

**In steps of the device's cycle.** The code (`unisono_core::player`) runs the
law once for each cycle of the device. Let $h$ be the length of a cycle,
$a = \kappa h$, $E$ the distance by which the position read is behind the
schedule, in frames, and $v$ the number of frames that a cycle reads beyond
what the schedule advances. One cycle is

$$v' = (1 - \sqrt2\,a)\,v + a^2 E, \qquad E' = E - v' .$$

The second equation is not computed: the position is advanced by what was
read, exactly, and $E$ is measured against the schedule again at the next
cycle. The matrix of the two equations has determinant $1 - \sqrt2\,a$ and
trace $2 - a^2 - \sqrt2\,a$, so the recursion is stable exactly for
$0 < a < \sqrt6 - \sqrt2 \approx 1.04$; the code holds $a$ at one half or
below. The pace as a whole, scheduled and corrected, is held within
$u_{\max}$ by limiting $v$, and a distance beyond a set number of frames is
not played away: the position jumps to the schedule.

About the recursion over the real numbers, in `Unisono.Model.Regulator`:

- A quadratic form of $(E, v)$, the area spanned by a state and the state
  after it, is multiplied by exactly $1 - \sqrt2\,a$ in every cycle
  (`energy_step`). For $0 < a \le \tfrac12$ it is positive definite and
  bounds the distance (`distance_le_energy`).
- From rest, as after a start or a jump, the distance after $k$ cycles is at
  most $\sqrt{12}\,(1 - \sqrt2\,a)^{k/2}$ times the distance at the start
  (`distance_from_rest`), and from any state it is bounded the same way by the
  form at the start (`distance_after`).
- With a pace that is wrong by $d$ frames a cycle, the state moves as without
  the error around the point where the distance is $\sqrt2\,d/a$
  (`stepWith_shift`), so that is where the distance tends.
- A cycle whose correction is at the limit $L$ starts at least
  $\sqrt2\,L/a$ from the schedule and ends $L$ nearer (`at_limit`), so the
  limit holds for no more cycles in a row than the distance holds limits.

About the code: planning a cycle returns for every state, schedule and reading
of the clock (`Unisono.Player.cycle_total`), and changes nothing of a receiver
but its regulator (`Unisono.Receiver.cycle_spec`). *Not yet stated in Lean:*
how far the computation in whole numbers is from the recursion in real
numbers, and that after the limit has let go it does not take hold again.

In simulation (`crates/unisono-sim/tests/timing.rs`), with the cycle lengths
taken from a device that is 120 parts per million off its nominal rate, the
remaining error is as the formula above says when the receiver ignores that
rate: $\sqrt2 \cdot 120\cdot10^{-6} / \kappa$, which is 42 microseconds for
$\kappa = 4$ per second.

**Large errors.** At a start and after a pause the error can be far larger
than the bound on the rate removes quickly. Slewing at the largest rate left,
$u$, takes $|e|/u$, and costs $w_{\mathrm{sync}}\,|e|^3 / (3 u N)$ for one
receiver. Jumping costs that receiver one gap, $w_{\mathrm{gap}}/N$, or nothing
when it is silent. It jumps when the first exceeds the second. An error that
all receivers share is no error of synchronization, and is not answered by each
receiver for itself: the sender moves the level.

In the code the threshold is a setting, in frames, and applies to a distance
either way. A jump back replays nothing: the frames that a receiver has given
to its device are behind its playhead and are not given again, so the receiver
plays silence until the position reaches the playhead.

### 6.5 The level

Write $\Gamma_r(\mu)$ for the rate of gaps of receiver $r$, and $\Phi_r(\mu)$
for the fraction of frames it misses, when its margin above its baseline and
lead is $\mu$. A level held at $\ell$ costs

$$J(\ell) \;=\; w_{\mathrm{lat}}\,\ell + w_{\mathrm{tgt}}\,(\ell - L_0)^2
+ \frac1N\sum_r \Bigl[w_{\mathrm{gap}}\,\Gamma_r(\ell - B_r - \Lambda_r)
+ w_{\mathrm{miss}}\,\Phi_r(\ell - B_r - \Lambda_r)\Bigr].$$

The level is one number and $J$ is minimized over a line, so no convexity is
needed: pause lengths with several typical values give several local minima.
A minimizer exists when $w_{\mathrm{lat}}$ or $w_{\mathrm{tgt}}$ is positive
and $w_{\mathrm{miss}}$ is.

Each receiver estimates $\Gamma_r$ and $\Phi_r$ from the delays it has seen and
reports them; the sender minimizes. A rate far out in the tail rests on few
events, so the estimates are posterior means under a prior for the tail, and a
receiver with little evidence reports high rates at low levels.

The level moves to another minimum only when the cost saved, over the time the
evidence covers, exceeds the cost of the move. It moves along a path that the
sender announces ahead, at a rate within the bound of section 6.4.

*Not yet stated in Lean.*

## 7. Assumptions at a glance

| Assumption | Section | Used for | Monitor |
|---|---|---|---|
| Oscillators: bounded frequency, bounded departure from a line | 1 | error of the fitted line | change of the fitted slope |
| Delay: never negative; a nearly undelayed packet in each half of the memory | 2.2 | the fitted line | height of window minima above the line |
| Stamps err toward delay | 2.2 | the fitted line | samples that lower the line by much |
| Smallest delays equal in both directions for equal sizes, up to an unknown constant | 2.3, 2.5 | the offset | half-sum of the two fitted lines |
| Device reports: bounded error of either sign, constant delay | 2.4 | device lines | residuals of reports |
| Delivery delay: baseline, deviation, pauses | 4 | level | histograms and records of each part |
| The laws of the delivery delay hold over the time the evidence covers | 6.5 | level | short-window against long-window estimates |
