# The model

This page states the problem unisono solves: the clocks, what can be measured
about them, the stream, the disturbances and the objective. Each statement is
a definition, an assumption about the world, or a claim. An assumption names
the quantity that monitors it at run time. A claim names its statement in
`lean/`, or says that it is not yet stated there. Symbols are defined where
they are used, and all times are in seconds.

## 1. Clocks

A host reads time from its **raw clock**, an oscillator that no time service
corrects. Write $C_h(t)$ for the reading of host $h$'s raw clock at true time
$t$. True time is never observed; only readings are.

The **fractional frequency** of host $h$ is $y_h(t) = \dot C_h(t) - 1$, the
amount by which its clock runs fast.

**Assumption (oscillators).** $|y_h| \le y_{\max}$, and $y_h$ changes slowly:
$|\dot y_h| \le a_h$. For the stochastic analysis $y_h$ is a random walk, whose
increment over a time $\Delta$ has variance $q_h \Delta$. *Monitor:* the
curvature of each estimated clock relation.

There is one sender $S$ and there are receivers $r = 1, \dots, N$. The
**offset** of receiver $r$ is $x_r(t) = C_r(t) - C_S(t)$, and its **relative
frequency** is $\dot x_r = y_r - y_S$.

An audio device counts frames. Write $P_d(t)$ for the count of device $d$ at
true time $t$, and $f_d$ for its nominal rate in frames per second. A device's
counter is a clock like any other, with its own fractional frequency.

**Symmetry.** Add one function $g(t)$ to every clock, $C_h \to C_h + g$. No
measurement below changes, because each compares two clocks at one event or
one clock at two events of the same packet. Nothing in unisono can therefore
depend on true time, and no host's clock is privileged by nature. The sender's
raw clock is the time base by convention.

## 2. Measurements

### 2.1 Two clocks of one host

Reading clock $A$, then clock $B$, then clock $A$ again gives the difference of
the two to within half the time between the two readings of $A$. This relates
the raw clock to the clocks in which a kernel or an audio system reports time.

### 2.2 A packet

The sender stamps a packet with the reading $t^{\mathrm{tx}}$ of its clock at
departure, and the receiver with the reading $t^{\mathrm{rx}}$ of its own clock
at arrival. Define the packet's **delay** $d$ as its transit time read on the
sender's clock. Then, exactly,

$$z \;=\; t^{\mathrm{rx}} - t^{\mathrm{tx}} \;=\; x_r(\text{arrival}) + d .$$

**Assumption (delay).** $d = \delta_r + \eta$, where $\delta_r$ is the smallest
delay of the path, constant while the path does not change, and $\eta \ge 0$
is the excess. The noise is one-sided: a packet is delayed, never early.
Among any $W$ consecutive packets at least one has $\eta \le \epsilon$.
*Monitor:* the spread of the smallest values of $z$ in successive windows,
after the fitted line is removed.

A sequence of such packets shows $x_r + \delta_r$ along its lower edge. One
direction alone therefore determines the relative frequency, and the offset up
to the constant $\delta_r$.

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

The second quantity, the round trip, shows that amount once the smallest round
trip has been seen, up to the change of the offset while the receiver held the
exchange.

### 2.4 One datagram at two receivers

When one datagram reaches receivers $r$ and $r'$, the difference of their
stamps is $x_r - x_{r'}$ plus the difference of the two delays. The sender's
clock and the moment of departure cancel. This holds for multicast on a wired
network.

### 2.5 A device

An audio system reports pairs $(p, T)$: the device's counter read $p$ when the
host's clock read $T$.

**Assumption (device reports).** The error $\nu$ of a report is two-sided and
bounded, $|\nu| \le \nu_{\max}$. Sound leaves a playback device a constant time
$D_d$ after its counter passes a frame, and entered a capture device a constant
time before. *Monitor:* the residuals of the reports against the device's
fitted line.

### 2.6 What cannot be observed

Three things stay outside every measurement above, and they bound what
software can promise:

- true time (section 1);
- for each receiver, half the difference of the smallest delays in the two
  directions;
- for each device, its constant delay $D_d$.

All three are constants. They shift the timing between loudspeakers by amounts
that are the same after every restart, as long as the path and the devices are
the same.

## 3. The stream

The sender's capture device counts frames from the start of a **timeline**; the
count is the frame's **index** $n$. The **capture time** $\tau(n)$ is the
reading of the sender's clock when the device's counter passed $n$, taken from
the sender's fitted line for its device (section 2.5).

The **level** $\ell$ is the latency every receiver of the stream holds. Frame
$n$ is to leave each receiver's device when the sender's clock reads
$\tau(n) + \ell$.

For receiver $r$, let $t^{\mathrm{out}}_r(n)$ be the true time at which frame
$n$ leaves its device. Its **timing error** is

$$e_r(n) \;=\; C_S\bigl(t^{\mathrm{out}}_r(n)\bigr) - \bigl(\tau(n) + \ell\bigr),$$

positive when the frame is late. The **synchronization error** between two
receivers is $e_r(n) - e_{r'}(n)$, and the **latency** of receiver $r$ is
$\ell + e_r(n)$.

Frame $n$ arrives at receiver $r$ with a **delivery delay** $D_r(n)$ after its
capture: everything from capture to the frame lying in the receiver's buffer.
The **margin** is $m_r(n) = \ell + e_r(n) - D_r(n)$. A frame with negative
margin is **missed**: it is due before it is there, and the receiver conceals
it. A **gap** is a run of missed frames longer than concealment covers.

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

Let $\bar L$ be the mean latency of the receivers. The cost per second is

$$w_{\mathrm{lat}}\,\bar L
\;+\; w_{\mathrm{tgt}}\,(\bar L - L_0)^2
\;+\; \frac{w_{\mathrm{sync}}}{N}\sum_{r}\,(L_r - \bar L)^2
\;+\; w_{\mathrm{gap}}\cdot(\text{gaps per second, summed over receivers}),$$

subject to a bound on how the playback rate may move (section 6.4).

The four weights and the target latency $L_0$ are parameters of a stream, and
no value of them is built in. A large $w_{\mathrm{tgt}}$ holds the latency at
$L_0$, which suits audio that accompanies video. With $w_{\mathrm{tgt}} = 0$
the latency follows the link. A gap is priced by its occurrence and not by its
length: a thousand gaps of a millisecond are not the same as one second of
silence.

## 6. What follows

### 6.1 The timing error has five parts

Receiver $r$ turns the due time $\tau(n) + \ell$, which is on the sender's
clock, into its own clock with its estimate $\hat x_r$ of the offset, and then
into a position of its device with its fitted line for the device. It follows
that

$$e_r \;=\; \underbrace{\epsilon^{\mathrm{est}}_r}_{\text{offset estimate}}
\;+\; \underbrace{\tfrac12\bigl(\delta^{\to}_r - \delta^{\leftarrow}_r\bigr)}_{\text{path asymmetry}}
\;+\; \underbrace{\epsilon^{\mathrm{dev}}_r}_{\text{device line}}
\;+\; \underbrace{D_{d(r)}}_{\text{device delay}}
\;+\; \underbrace{\epsilon^{\mathrm{reg}}_r}_{\text{regulator}} .$$

The second and fourth parts are the constants of section 2.6. The delivery
delay of section 4 appears nowhere: when the schedule comes from clocks,
jitter and pauses of the network do not move the playback rate. They act on
the margin only, and the level answers them (section 6.5). A design that
steers by the depth of its buffer has the delay process inside its loop and
must trade synchronization against roughness of the rate; here that trade
does not arise.

### 6.2 Synchronization does not depend on the sender's clock

Each receiver estimates $x_r + \delta_r$ by fitting a line to its packets
(section 6.3). Suppose the sender's clock is replaced by $a + (1+b)\,C_S$,
for constants $a$ and $b$. Every stamp $t^{\mathrm{tx}}$ changes, and every
receiver's fitted line changes by the same affine function, whatever its
settings and whichever packets it used. The differences $e_r - e_{r'}$ do not
change.

*Lean:* `Unisono.Model.LineFit.schedule_invariant`, from `add_affine` (adding
an affine function of the times to the values adds it to the fit) and
`reparametrize` (an affine change of the times rescales the slope and keeps
the value).

So a constant offset and a constant rate error of the sender's clock have no
effect on synchronization. A *change* of the sender's frequency does reach the
fits, and two receivers answer it alike exactly when their fits weight the past
alike. Receivers with the same settings therefore stay together through it.
Between receivers with different settings a frequency step of $\Delta f$
appears as a transient difference of the order of $\Delta f$ times the
difference of their memory lengths: about a microsecond for a step of one part
per million and memories that differ by a second.

This is why each receiver estimates on its own. A joint estimator of all
clocks would separate the motion common to the receivers from their
differences, and for receivers with equal settings the separate fits already
are that joint estimate in the differences.

### 6.3 The estimator

For one receiver, the quantity to track is $\theta(t) = x_r(t) + \delta_r$,
seen through the values $z$ of section 2.2.

**Selection.** Packets are grouped into windows by index. In each window the
packet with the smallest $z$, after the current fitted slope is removed, is
kept. By the delay assumption its excess is at most $\epsilon$. Selection
commutes with the changes of section 6.2.

**Fit.** The estimate is the line that minimizes the squared residuals of the
kept samples, a sample that is $k$ windows old weighted by $\lambda^k$ with
$0 < \lambda < 1$:

$$(\hat\theta, \hat\rho) \;=\; \arg\min_{\theta,\rho}\;
\sum_j \lambda^{k_j}\,\bigl(z_j - \theta - \rho\,(t_j - t)\bigr)^2 .$$

Here $t$ is the time for which the estimate is wanted, $t_j$ and $z_j$ are the
time and value of sample $j$, and $k_j$ is its age in windows. The state the
receiver keeps is the set of weighted sums that determine the minimizer. With
samples at fewer than two distinct times no slope is determined, and the
receiver keeps the slope it had.

Claims, with $S_m = \sum_j \lambda^{k_j}(t_j - t)^m$:

- *The sums give the minimizer.* The line computed from the weighted sums has
  the smallest weighted sum of squared residuals. *Lean:*
  `Unisono.Model.LineFit.cost_le`. That the sums can be kept window by window
  (older weights scaled by $\lambda$, the reference time moved, a sample
  added) is `moment_shift`, `moment_scale` and `moment_insert`.
- *The error is bounded by quantities the receiver has.* If every kept sample
  has excess at most $\epsilon$ and the true $\theta$ differs from a line by at
  most $\tfrac12 a\,(t_j - t)^2$ at each sample, then

  $$|\hat\theta - \theta(t)| \;\le\; \epsilon\,\sqrt{\frac{S_0 S_2}{S_0 S_2 - S_1^2}}
  \;+\; \frac{a}{2}\,\sqrt{\frac{S_2 S_4}{S_0 S_2 - S_1^2}} .$$

  *Lean:* `Unisono.Model.LineFit.error_bound`. The receiver evaluates the
  right-hand side from its own sums and exports it, so every clock relation
  carries its stated error.
- *The past is forgotten.* A sample's weight falls geometrically, so after a
  restart, a pause or a corrupted state the estimate depends on fresh samples
  alone after a number of windows that is fixed by $\lambda$ and the width of
  the numbers. *Lean:* stated with the implementation.

The discount $\lambda$ sets the memory. A long memory averages more noise
($\epsilon$ counts less) and follows a changing frequency worse ($a$ counts
more); the bound above shows both. $\lambda$ is chosen where the two terms
balance, from the measured $\epsilon$ and $a$.

**Reference.** Under the stochastic model of section 1 with Gaussian noise on
the kept samples, the estimator with the smallest mean squared error is the
Kalman filter of that model. The simulator runs it beside the discounted fit
under every published set of assumptions, and the ratio of their errors is
reported. *Not stated in Lean.*

**The constant.** $\delta_r$ is estimated apart, from the exchanges of
section 2.3, as half the smallest round trip. It is a property of the path and
changes only when the path does.

### 6.4 The regulator

The receiver's resampler reads the stream at a rate $1 + u$ relative to its
device. The schedule of section 3 asks for a position and a rate $1 + \hat u$,
both from the fitted lines. Let $e$ be the time by which the resampler is
behind the schedule and $\tilde u = u - \hat u$. Then $\dot e = -\tilde u$, and
the regulator is

$$\dot{\tilde u} \;=\; \kappa^2 e \;-\; \sqrt2\,\kappa\,\tilde u ,
\qquad |\tilde u| \le u_{\max} .$$

For the cost $w_{\mathrm{sync}}\,e^2 + w_{\mathrm{rough}}\,\dot u^2$ with the
error observed exactly, this law is optimal with
$\kappa = (w_{\mathrm{sync}} / w_{\mathrm{rough}})^{1/4}$; it has damping
$1/\sqrt2$.

The estimated rate $\hat u$ is fed forward. Under a constant drift the error
therefore goes to zero without an integrator in the loop: the fit of section
6.3 supplies what an integrator would have to learn.

**The bound on the rate.** A change of the playback rate is heard as a change
of pitch when it is large and fast enough. $u_{\max}$ and $\kappa$ are set so
that the rate stays below that. In steady state the constraint is far from
active: an estimate that moves by a few microseconds per window moves the rate
by tens of parts per million, and a change of pitch is heard at about a
thousand.

Claims, for the regulator in steps of the device's cycle, of length $h$:
stable for $0 < \kappa h < \sqrt2$; with constant $\hat u$ the error tends to
zero; from any state it leaves the limit $u_{\max}$ after a bounded time.
*Lean:* stated with the implementation.

**Large errors.** At the start, after a pause and when the level moves, the
error can be far larger than the rate limit removes quickly. Slewing at
$u_{\max}$ takes $|e|/u_{\max}$, during which this receiver is out of step
with the others, at a cost of $w_{\mathrm{sync}}\,|e|^3 / (3 u_{\max})$.
Jumping costs one gap, or nothing when the receiver is silent. The receiver
jumps when the first exceeds the second.

### 6.5 The level

Write $\Gamma_r(\mu)$ for the rate of gaps of receiver $r$ when its margin
above its baseline is $\mu$. The level minimizes the cost of section 5 with
the latency held at the level:

$$\ell^* \;=\; \arg\min_{\ell}\; w_{\mathrm{lat}}\,\ell + w_{\mathrm{tgt}}\,(\ell - L_0)^2
+ w_{\mathrm{gap}}\sum_r \Gamma_r(\ell - B_r) .$$

The level is one number and the minimization is over a line, so no convexity
is needed: pause lengths with several typical values give a cost with several
local minima, and the smallest is taken.

Each receiver estimates $\Gamma_r$ from the delays it has seen and reports it;
the sender minimizes and announces $\ell$. A rate far out in the tail rests on
few events, so $\Gamma_r$ is a posterior mean under a prior for the tail, and a
receiver with little evidence reports a high rate at low levels.

The level moves at no more than the rate limit of section 6.4. It rises at
that limit as soon as the minimizer rises.

*Lean:* the bounds and the rate of the level's path are stated with the
implementation.

## 7. Assumptions at a glance

| Assumption | Used for | Monitor |
|---|---|---|
| Oscillators: bounded frequency, bounded rate of change | error bound of the fit | curvature of each fitted line |
| Delay: one-sided, a nearly undelayed packet in every window | selection | spread of window minima about the fit |
| Smallest round trip has been seen | the constant of each path | drops of the smallest round trip |
| Device reports: bounded two-sided error, constant delay | device lines | residuals of reports |
| Delivery delay: baseline, deviation, pauses | level | histograms and records of each part |
| Stationarity over the memory of the tail estimate | level | short-window against long-window estimate |
