# unisono

unisono streams uncompressed pulse-code modulation (PCM) audio over User
Datagram Protocol (UDP) to multiple receivers and synchronizes playback across
wired and wireless links. It is designed from the ground up for small
processing quanta and real-time operation.

**Status: early development. Nothing here can be used yet.**

Unisono is written in Rust, with its pure protocol and timing core
(`crates/unisono-core`) translated to Lean via
[Aeneas](https://github.com/AeneasVerif/aeneas) so that formal proofs target
the production implementation directly.

## Proof and test status: proved vs. tested

Unisono separates what is formally proved in Lean (in `Unisono.Spec` and on the
translated core) from supplementary side-model analyses and what is checked by
simulation and integration tests (see `PRINCIPLES.md`):

- **Formally proved in Lean (on `Unisono.Spec` and the translated Rust core):**
  - Panic-free, overflow-free totality, bounded-loop termination, packet codec
    round-trips, exact four-timestamp NTP arithmetic, and state-machine
    invariants of the translated production core (`lean/Unisono/*.lean`).
  - Properties of the translated core composed as a `Unisono.Spec.Solution` in
    `lean/Unisono/Solutions/Core.lean` (a Lean composition of `unisono-core`
    functions rather than a proof about `unisono-runtime`): causality (strictly
    local observations), communication-graph membership (`UsesGraph`) and exact
    degeneration to star topology (`IsStar`, zero peer messages, and identical
    single-mode playback when no peers are configured), non-Zeno progress and
    playback-request liveness under `World.WithinBounds`, within-block
    playback-speed bounds under `World.WithinBounds` (plus a conditional
    adjacent-block step bound when `jump >= 3`, no silence restart, and no
    `u64::MAX` overflow), and component-level exactness on noiseless constant
    inputs (`ntp_exchange`, `KalmanFilter` zero-innovation fixed point,
    `ModalPlayer.cycle` unity step).
  - Topology-dependent lower bounds and a two-sided Star-vs-Peer asymmetry
    separation directly in `Unisono.Spec` (`lean/Unisono/Spec/Limits.lean`),
    plus end-to-end objective bounds for the abstract real-valued reference
    `Unisono.Solutions.FixedDelay` under `World.WithinBounds`.
  - The exact cost of `Unisono.Solutions.FixedDelay` in an ideal constant world
    with any number of receiving hosts
    (`lean/Unisono/Solutions/FixedDelay/Exact.lean`): each speaker plays every
    frame late by half the difference between the delay from the sender to
    its host and the delay back. The theorem assumes zero weights on
    latency and roughness.
  - The definition of optimality in expected cost (`OptimalWithin` in
    `lean/Unisono/Spec/Optimality.lean`). Under the generative model it is
    stated for every member (`GenerativeWorld.OptimalWithin`): a member
    that a statement does not cover has the margin `⊤` in the statement. The
    solutions compared at a member depend on that member alone
    (`GenerativeWorld.measurableCost`: those whose cost in the member is a
    measurable function of what is drawn). Also the
    generative model `GenerativeWorld`, with checks of its definitions and a random world that
    satisfies it (a member with no pauses and no clock wander).
  - In a member of `GenerativeWorld` with no pauses, no clock wander, no
    spread of clock rates and exact device timestamps, almost every outcome is an ideal constant world
    and satisfies `World.WithinBounds`
    (`lean/Unisono/Spec/Models/GenerativeNoiseless.lean`), so the theorems
    about those models apply to it.
  - Every noiseless member of `GenerativeWorld` has a random world, for any
    hosts and speakers (`lean/Unisono/Spec/Models/GenerativeCanonical.lean`).
  - Every member of `GenerativeWorld` whose clocks do not wander and whose
    audio devices report exact timestamps has a random world, for any hosts
    and speakers (`lean/Unisono/Spec/Models/GenerativePauses.lean`). Its
    links and its hosts may pause, at any rates and with any laws of the
    lengths, and the mean rates of its clocks may be spread. The pauses come
    from a random process constructed in
    `lean/Unisono/Spec/Models/PauseProcess.lean`. A host that pauses
    handles the events of its audio devices after its backlog. In every
    random world of such a member whose hosts never pause, almost every
    outcome has clocks at constant rates and hosts that handle the events
    of their audio devices when they occur.
  - In every random world of a member of `GenerativeWorld`, the paused times
    of all links and hosts have the same law
    (`lean/Unisono/Spec/Models/GenerativePauseLaw.lean`), and in almost
    every outcome all links and hosts are without a backlog together during
    periods of any length, again and again
    (`lean/Unisono/Spec/Models/GenerativeIdle.lean`). The long-run average
    of a bounded quantity over the independent cells of the process of
    pauses is its mean (`lean/Unisono/Spec/Models/ErgodicCells.lean`). Among
    messages sent from one host to another at equally spaced true times, the
    fraction that take longer than a given time converges, in almost every
    outcome of every random world, to a probability that depends only on the
    member (`lean/Unisono/Spec/Models/GenerativeLate.lean`).
  - A star solution's costs in a world and in the same world with the links
    to and from the sender shifted add up to at least twice the cost of half
    the shift (`lean/Unisono/Spec/StarShift.lean`), for any number of hosts.
    The same holds without assuming that the solution plays every frame or
    that its run keeps going, for a solution whose position advances by one
    frame per output sample within a bound below one, when the weight of
    missed samples is large enough
    (`lean/Unisono/Spec/ShiftedPlayback.lean`): the missed samples pay for
    the frames that are never played (`lean/Unisono/Spec/Skips.lean`).
  - A bound for the baseline against solutions through the sender
    (`Unisono.Solutions.FixedDelay.within_starMargin` in
    `lean/Unisono/Solutions/FixedDelay/StarMargin.lean`). It does not make
    the baseline optimal: its margin is finite only in noiseless members,
    which are the members with every disturbance switched off. A star
    solution is one whose hosts exchange messages only with the sender. The theorem is
    stated for every member of `GenerativeWorld`, with the margin `⊤` for
    every member that it does not cover. The compared star solutions
    (`GenerativeWorld.StarSolutions`) are those with measurable cost that
    keep the speed bound: their position advances by one frame per output
    sample within a bound `u < 1`, at every step of continuous playback
    (`Solution.WithinStep`). Nothing is assumed about which frames they
    play. In every noiseless member within the baseline's
    delivery margin in which the weight of missed samples is large enough
    (`GenerativeWorld.MissedWeightPays`), with any number of hosts and
    speakers, the expected cost of `Unisono.Solutions.FixedDelay` exceeds
    that of no compared star solution by more than the sum of the weights of
    synchronization and tracking times `ρ³ / (4 Θ)`, where `ρ` is the sum
    over the speakers of the least round-trip time between the sender and the
    speaker's host and `Θ` bounds the clock offsets. The theorem needs zero
    weights on latency and roughness, no speaker on the sender's host, and a
    baseline whose slew is at most `u`.
  - The controller (`Unisono.Solutions.Controller`): the sender announces a
    level with every block, the latency that every speaker is to hold, and
    the hosts estimate the sender's clock and the clocks of their audio
    devices as lines. In a world whose clocks of hosts and of audio devices
    run at constant rates, each its own, with the level held, the position
    that is due at an output sample is the one captured the level divided by
    the rate of the sender's clock, plus the asymmetry of the speaker's
    host, before the sample leaves. When links pause and hosts do not, an
    output sample plays that position if the message of the capture block it needs
    took less than the sample's margin, and plays nothing of the source
    otherwise (`Unisono.Solutions.Controller.plays_under_pauses` in
    `lean/Unisono/Solutions/Controller/Pauses.lean`, with the margin in
    `lean/Unisono/Solutions/Controller/HeldLevel.lean`). Without pauses it
    plays every frame at that latency
    (`Unisono.Solutions.Controller.playsAtLatencies` in
    `lean/Unisono/Solutions/Controller/Exact.lean`). When the level
    changes, and each block starts at the level at which the block before
    it ended, every position is played at the latency of its own level,
    if the capture block that it needs arrived before the request
    (`Unisono.Solutions.Controller.speaker_plays_of_levels` in
    `lean/Unisono/Solutions/Controller/HeldLevel.lean`). A level rule with
    such levels, which steps the level against the needs that clock
    queries report, is defined and shown to be continuous from block to
    block (`Unisono.Solutions.Controller.steppedLevel` in
    `lean/Unisono/Solutions/Controller/SteppedLevel.lean`). The need of a
    capture block at a speaker is a level at which the block is in time,
    and a host can compute it from its own estimates
    (`Unisono.Solutions.Controller.arrival_lt_asked_of_needOf_le` and
    `measuredNeed` in `lean/Unisono/Solutions/Controller/Needs.lean`). It
    is not yet proved which needs reach the sender, what the rule does
    with them, or what a level that changes costs. One solution puts the
    parts together for worlds in which clocks wander and links and hosts
    pause. Its hosts take their timing from what they observe themselves:
    the capture schedule from the sender's readings at the handovers, the
    time at which an output sample leaves from the host's readings at the
    requests, and the sender's clock from the arrivals of the blocks. A
    host plays only where a clock exchange confirms its estimate of the
    sender's clock and the block that is due was handed over on time by
    its timestamp (`Unisono.Solutions.Controller.checkedReading` in
    `lean/Unisono/Solutions/Controller/Timing.lean`). Its
    level changes within a block by at most a share of the block's time
    from one frame to the next, so the schedule on which positions are due
    is continuous and advances in every block of every world, also when
    the sender's host was busy and handles several handovers at the same
    time (`Unisono.Spec.knotStep` in
    `lean/Unisono/Solutions/Controller/Knots.lean`,
    `Unisono.Solutions.Controller.dueSlope_pos`, `dueEdge_succ` in
    `lean/Unisono/Solutions/Controller/DueSchedule.lean`). Its
    playback follows the position that is due within the step bound. In
    every world its hosts exchange messages only with the sender, it keeps
    the step bound, and the position that a host chooses satisfies an
    exact equation between the schedule, the announced level and the
    host's estimate of the sender's clock, with an exact expression for
    the error of that estimate
    (`Unisono.Solutions.Controller.combined`, `combined_withinStep` in
    `lean/Unisono/Solutions/Controller/Combined.lean`, `timed_chosen` in
    `lean/Unisono/Solutions/Controller/Timing.lean`). For any solution
    whose playback follows what it chooses in this way, the missed samples
    and the discontinuities are bounded by the number of output samples
    that play nothing and by how far the steps of what it chooses differ
    from one frame beyond the step bound, summed
    (`Unisono.Spec.Solution.followed_sum_missedAt_le` in
    `lean/Unisono/Spec/FollowerRun.lean`). In a world without loss, an
    output sample of the combined solution whose request is handled before
    it leaves plays nothing only when the stream has not yet reached the
    host or a block that the output sample needs arrived after the request
    (`Unisono.Solutions.Controller.followed_silent` in
    `lean/Unisono/Solutions/Controller/Silent.lean`). The latency of the
    position that a host chooses is, in every world, the announced level
    plus four errors that each have one cause: of the capture schedule, of
    the delay of the block that the host's estimate rests on, of the host's
    slope, and of the time at which the host expects the output sample to
    leave (`Unisono.Solutions.Controller.timed_chosen_parts` in
    `lean/Unisono/Solutions/Controller/ChosenLatency.lean`). No cost of the
    combined solution is bounded yet. The cost of a held
    level is at most the cost of the speakers' latencies plus a multiple of
    the late rate, the long-run number of output samples per second whose
    block is late (`Unisono.Solutions.Controller.cost_le_of_heldLevel` in
    `lean/Unisono/Solutions/Controller/Cost.lean`). These theorems hold in
    one outcome, and they assume of the outcome that two clock exchanges of
    each receiving host escape every pause. In every random world of a
    member whose clocks do not wander, whose audio devices report exact
    timestamps and whose hosts never pause, that holds in almost every
    outcome
    (`Unisono.Solutions.Controller.ae_twoUndelayed` in
    `lean/Unisono/Solutions/Controller/Undelayed.lean`). In such a random
    world the long-run fraction of capture blocks whose message is slower
    than the least margin of a speaker is, in almost every outcome, a
    probability of the member
    (`Unisono.Solutions.Controller.ae_tendsto_slowBlocks` in
    `lean/Unisono/Solutions/Controller/LateBlocks.lean`). The late rate is
    at most the mean over the speakers of that probability times the sum of
    the speaker's output samples per second and the capture blocks per
    second (`Unisono.Solutions.Controller.ae_lateRate_le` in
    `lean/Unisono/Solutions/Controller/LateRate.lean`). The expected cost of
    the controller at a held level is at most the mean of an explicit
    function of what is drawn, and that mean is finite
    (`Unisono.Solutions.Controller.expectedCost_le_heldLevelCost` and
    `lintegral_heldLevelCost_lt_top` in
    `lean/Unisono/Solutions/Controller/ExpectedCost.lean`). The controller
    does not keep the speed bound of the compared solutions. With a limiter,
    which makes an output sample play nothing of the source when its step
    would break the bound, it keeps the bound in every world, and its
    expected cost at a held level has a finite bound of the same form
    (`Unisono.Solutions.Controller.limited_withinStep` and
    `expectedCost_le_limitedCost` in
    `lean/Unisono/Solutions/Controller/Limited.lean`). For every
    solution whose hosts exchange messages only with the sender, in every
    outcome of every member, an output sample plays a position only if a
    message sent at the handover of the last capture block it needs arrived
    before the request of its playback block
    (`Unisono.Spec.GenerativeWorld.Prior.arrival_lt_of_plays` in
    `lean/Unisono/Spec/Models/GenerativeEarliest.lean`), and a stretch of
    output samples in which no newer position can be played costs missed
    samples or discontinuities (`Unisono.Spec.stall_le_of_le` in
    `lean/Unisono/Spec/Stall.lean`). Paused time of the link from the sender
    that begins in a short interval gives such a stretch, whatever backlogs
    exist and also when the clocks wander, and until it can be noticed a
    solution plays as in the world without it
    (`Unisono.Spec.GenerativeWorld.Builds.stall_le_of_sameExcept` in
    `lean/Unisono/Spec/Models/GenerativeLinkPause.lean`). The frames that a
    speaker holds beyond the position it plays are paid for with latency
    (`Unisono.Spec.GenerativeWorld.Builds.le_sum_add_loss` in
    `lean/Unisono/Spec/Models/GenerativeRoom.lean`). In every random world
    of every member, what a link pauses within a period is independent of
    the rest of the draw, and drawing it again from an independent copy of
    the probability space gives a random world of the same member
    (`Unisono.Spec.GenerativeWorld.Prior.indepFun_linkOutside` and
    `Prior.prior_resample` in
    `lean/Unisono/Spec/Models/GenerativeResample.lean`). The same holds
    for the pauses of all links together, which leaves the clocks, the
    pauses of the hosts and the audio devices of the first outcome in
    place (`Prior.prior_resampleLinks`
    in `lean/Unisono/Spec/Models/GenerativeResamplePauses.lean`). These
    are combined into a lower bound on the expected cost, in every member,
    of every solution through the sender that keeps the step bound and
    whose playback is a measurable function of what is drawn: the expected
    cost is at least the mean, over the outcomes, of a bound for the
    clocks of the outcome
    (`Unisono.Spec.GenerativeWorld.lintegral_fixedClockBound_le` in
    `lean/Unisono/Spec/Models/GenerativeClockMean.lean`). For members
    whose clocks do not wander, whose audio devices report exact
    timestamps and whose hosts never pause that bound is evaluated in
    closed form, as a level program
    per second that trades the latency of the room that a solution keeps
    against what a pause costs with that room
    (`Unisono.Spec.GenerativeWorld.lintegral_steadyBound_le` in
    `lean/Unisono/Spec/Models/GenerativeSteadyBound.lean`). The bound is
    not yet compared with the cost of the controller, it is not evaluated
    for members whose clocks wander, and the part of a lower bound that
    comes from the unknown split of each round trip is proved only for
    noiseless members. The controller does not yet change its pace
    smoothly or choose the level.
- **Supplementary analytical theorems (side models outside `Unisono.Spec`):**
  - Component and centralized/oracle analyses in `lean/Unisono/Model/*` and
    `lean/Unisono/Analysis/*` (per-cycle quadratic modal control on
    `multiCycleCost`, Thomson's principle for real-valued graph-Laplacian Best
    Linear Unbiased Estimation (BLUE) under uncorrelated edge errors, and
    continuous-time Campbell pause-margin formulas). These serve as analytical
    references alongside `Unisono.Spec`, never as replacements for end-to-end
    proofs on `Unisono.Spec.Objectives`.
- **Open (not formally proved):**
  - No theorem currently connects a run of `Core.solution` to any of the six
    `Unisono.Spec.Objectives` in any model (including `IdealConstantWorld`,
    `World.WithinBounds`, `StationaryNetworkDisturbances`,
    `SecondOrderMoments`, `StochasticWorld`, and `GenerativeWorld`).
  - No solution is proved optimal under `GenerativeWorld`.
    The one bound of that form compares only solutions whose hosts exchange
    messages with the sender alone, in noiseless members; with two or more
    receiving hosts, a solution that also uses links between them can do
    better. No lower bound on expected cost is proved for such solutions, or
    for members with pauses or clock wander.
    Random worlds are constructed for every member whose clocks do not
    wander and whose audio devices report exact timestamps; a random world
    with clock wander or with errors of the timestamps is not constructed in
    Lean. The expectation that a solution loses nothing in the long run by
    not being told the numbers of its member is not proved.
  - Unconditional `Solution.WithinSpeed` across all block boundaries (including
    silence restarts and arbitrary `jump` values) for `Core.solution` remains
    open.
  - Quantitative integer-to-real accuracy bounds linking the fixed-point core
    estimators (`KalmanFilter`, `SlidingMinRtt`, and the integer `LDL^T` BLUE
    solver on multi-peer graphs) to real-valued models remain open (`Kalman`
    positive-semidefiniteness theorems hold via explicit clamping).
- **Tested by simulation and integration checks (outside Lean proofs):**
  - Multi-seed true-time simulation (`crates/unisono-sim`) driving the shipped
    `unisono-runtime` SPSC-ring pipelines over serialized v2 UDP datagrams with
    oscillator drift, device timestamp jitter, responder send latency, link
    delay, jitter, pauses, outages, and packet loss, scoring all six
    `Unisono.Spec.Objectives` strictly from rendered PCM output.
  - Concurrency interleaving checks (Loom) on the lock-free single-producer
    single-consumer (SPSC) rings, machine-code inspection (`crates/reachable`,
    `crates/cycle-cost`) confirming real-time threads perform no syscalls,
    allocations, or panics, loopback UDP tests, and container tests against
    PipeWire and Advanced Linux Sound Architecture (ALSA).
  - Floating-point components outside `crates/unisono-core`: the adaptive
    latency chooser (`crates/unisono-runtime/src/level.rs`), resampling and gap
    concealment (`crates/unisono-dsp`), and operating-system input/output.

## What works

Built and tested on Linux, without audio hardware:

- A sender and receivers as processes (`unisono send`, `unisono receive`),
  over UDP, with a virtual software device
  (`crates/unisono-runtime/src/virtual_device.rs`) that captures a test signal
  and one that plays to nothing at its own rate, or with PipeWire or ALSA when
  built with the feature `pipewire` or `alsa`.
- Unified peer-assisted and star clock synchronization in `crates/unisono-core`
  (`sync.rs`, `min_rtt.rs`, `kalman.rs`, `blue.rs`, `player.rs`): receivers
  combine four-timestamp round-trip time (RTT) exchanges with the sender and
  optional direct peer receivers, sliding-window minimum-RTT selection,
  fixed-point graph-Laplacian BLUE, two-state Kalman filtering, and decoupled
  common-mode and differential-mode playback regulation. When no peers are
  configured, synchronization degenerates structurally and mathematically to
  star mode with zero peer traffic.
- The receivers measure the latency each stretch of the stream needed to arrive
  in time and report it; the sender chooses a shared latency from those reports
  (`crates/unisono-runtime/src/level.rs`) and ramps it along a schedule that
  every receiver follows.
- A receiver requests retransmission of frames from lost packets
  (`crates/unisono-runtime/src/retransmission.rs`), and the sender retransmits
  kept packets on request; frames that still do not arrive in time are
  concealed.
- Wait-free counters, gauges, and histograms exported in the Prometheus text
  format (`--metrics`, `crates/unisono/src/metrics.rs`), including counters
  that monitor model assumptions at run time.
- A C interface (`crates/unisono-c`, `include/unisono.h`): a driver hands a
  sender the frames of its capture device, or has a receiver fill the frames of
  its playback device, from the device's own cycle.

The tests run on x86-64 and on 64-bit ARM, and those of the core, the
signal processing and the metrics also on ARMv7 without hardware floating
point. Not built yet: platforms other than Linux (everything but the audio
systems compiles for macOS; its kernel stamps no departures, and the timing
there is not tested), and measurements on physical audio hardware: the ALSA and
PipeWire devices are tested against PipeWire in containers.

`docs/specification.tex` (`docs/specification.pdf`) and `lean/Unisono/Spec`
define the formal problem and objectives, `PRINCIPLES.md` states the
design and proof principles, `docs/theorems.md` lists what is proved,
`docs/protocol.md` specifies the version 2 wire protocol, and `docs/model.md`
records earlier design notes.

## Terminology

In the formal specification (`docs/specification.tex` and `lean/Unisono/Spec`),
a directed **link** $(i, j)$ between host $i$ and host $j$ represents the
entire end-to-end path between the application's send call on host $i$ and
receive call on host $j$. It includes both hosts' kernel network stacks,
drivers, network interface cards (NICs), switches or wireless access points
(APs), and the physical wired or wireless medium. Consequently, distinct links
that share a host or a wireless medium can experience correlated transmit or
receive jitter.

## World variables

The formal framework (`lean/Unisono/Spec/World.lean`,
`lean/Unisono/Spec/Models/Delays.lean`) separates the system under design
(`Solution`) from the **world** (`World`), which contains everything outside a
solution's control. **Disturbances** are the external factors acting on the
world's clocks, audio devices, and network links—including oscillator drift and
frequency noise, device timestamp errors, capture handoff and playback request
timing, and network baseline drift, per-packet jitter, pauses, outages, and
individual packet drops.

| Component | Formal variable (Lean) | Description |
|---|---|---|
| True time | $t \in \mathbb{R}$ (`Time`) | Physical time in seconds; never directly observed by any host. |
| Nominal rate and topology | $\rho > 0$ (`World.rate`), `sender`, `host` | Common nominal sample rate in frames per second, the sender host, and the host driving each of the $R$ speakers $r \in \{0, \dots, R - 1\}$. |
| Host clocks | $C_i(t)$ (`World.clock`) | Continuous, strictly increasing clock reading on host $i$ at true time $t$, with clock phase $\phi_i(t) = C_i(t) - t$ subject to rate drift and oscillator frequency noise. |
| Capture device | $c(n), f(b), h(b), \hat c(b)$ (`World.source`) | True capture time $c(n)$ of frame $n$, first frame $f(b)$ of block $b$, true time $h(b)$ at which the sender host handles the handover of block $b$, when its last frame is captured or later, and reported host-clock timestamp $\hat c(b)$ (subject to timestamp error). |
| Playback devices (speakers) | $o_r(k), g_r(b), a_r(b), \hat o_r(b)$ (`World.speaker`) | True output time $o_r(k)$ of sample $k$ on speaker $r$, first sample $g_r(b)$ of block $b$, true time $a_r(b)$ at which the host handles the request of block $b$ (an output sample of the block that has left by then plays nothing of the source), and reported host-clock timestamp $\hat o_r(b)$. |
| Target latency | $L^*(n)$ (`World.target`) | Application-supplied target latency for frame $n$ in lip-sync mode, delivered to the sender with the frame. |
| Link delivery | $\mathrm{deliver}_{ij}(s, q)$ (`World.network`) | Arrival time (or drop) of the $q$-th message sent from host $i$ to host $j$ at true time $s$; decomposed by `Link` into the four network disturbances below. |
| Slow baseline delay | $B_{ij}(u) > 0$ (`Link.baseline`) | Minimum transit time of directed link $(i, j)$ at release time $u$, slowly varying (Lipschitz). |
| Per-packet jitter | $J_{ij}(u, q) \ge 0$ (`Link.jitter`) | Excess delay above baseline for message $q$ released at true time $u$, with exponential upper tails; in `SecondOrderMoments`, decomposed into shared transmit jitter $J^{\mathrm{tx}}_i(u)$, shared receive jitter $J^{\mathrm{rx}}_j(u)$, and link-specific per-packet jitter $J^{\mathrm{own}}_{ij}(u, q)$. |
| Pauses and outages | `Link.pauses` (`Pause`) | Time intervals $[t_0, t_0 + H)$ of duration $H > 0$ during which a link either holds messages back and releases them at $t_0 + H$ (a **pause**) or drops every message released during the interval (an **outage**). |
| Individual packet drops | `Link.lost` | Set of message indices $q \in \mathbb{N}$ dropped individually on link $(i, j)$. |

## Models

All formal specification results are stated under one of the six approved
models in `lean/Unisono/Spec/Models` (see `PRINCIPLES.md` and
`docs/specification.tex`):

| Model | Scope | Description | Motivation | File |
|---|---|---|---|---|
| `IdealConstantWorld` | Deterministic full-world (satisfies `World.WithinBounds`) | Unit-rate clocks with arbitrary constant initial offsets, exact nominal-rate devices with fixed block sizes, zero handoff delay, constant request lead, exact timestamps, lossless constant per-link delays (`Symmetric` or `Asymmetric` subclasses), and constant target latency. | Noiseless baseline for exact fixed-point component checks on `unisono-core` and for the two-sided Star-vs-Peer asymmetry separation in `Unisono.Spec.Limits`. | [`lean/Unisono/Spec/Models/Ideal.lean`](lean/Unisono/Spec/Models/Ideal.lean) |
| `Bounds` (`World.WithinBounds`) | Deterministic worst-case full-world (plus `AlmostSurelyWithin`) | Uniform bounds on clock and device rate errors, device timestamp errors, capture handoff delay, playback request lead, block sizes, per-link minimum/maximum delays, and consecutive packet drops. | Worst-case guarantees for non-Zeno progress, playback-request liveness, within-block speed bounds, and deterministic offset and drift bounds. | [`lean/Unisono/Spec/Models/Bounded.lean`](lean/Unisono/Spec/Models/Bounded.lean) |
| `StationaryNetworkDisturbances` | Probabilistic network-only | Per-directed-link $(i, j)$ slow Lipschitz baseline, nonnegative per-packet jitter $(u, q)$ reaching arbitrarily close to zero with exponential upper tails, pause and outage episode arrival rates and finite-mean length distributions, individual drop probabilities $< 1$, and joint stationarity and mixing across all links (no cross-link independence assumed). | Captures tail delays, pauses, outages, and heterogeneous wired/wireless topologies that govern missed samples, discontinuities, and playout latency selection. | [`lean/Unisono/Spec/Models/Delays.lean`](lean/Unisono/Spec/Models/Delays.lean) |
| `SecondOrderMoments` | Probabilistic moment model (continuous timing noise) | Square-integrable host clocks and audio devices following band-limited IEEE Std 1139-2008 power-law frequency noise (white $h_0$, flicker $h_{-1}/f$, and random-walk $h_{-2}/f^2$ over Fourier frequency $f \in [f_{\mathrm{lo}}, f_{\mathrm{hi}}]$), additive per-packet link jitter ($J^{\mathrm{tx}}_i + J^{\mathrm{rx}}_j + J^{\mathrm{own}}_{ij}$) with unconstrained transmit/receive cross-correlations, and white device timestamp errors. | Captures first- and second-moment structure—including shared host-stack and wireless-medium jitter correlations and co-located oscillators—driving synchronization, tracking, and roughness. | [`lean/Unisono/Spec/Models/SecondOrder.lean`](lean/Unisono/Spec/Models/SecondOrder.lean) |
| `StochasticWorld` | Probabilistic composite full-world | Combines `StationaryNetworkDisturbances` and `SecondOrderMoments` over a shared per-link decomposition, together with deterministic capture-handoff, playback-request-lead, and block-size bounds across every realization. | Complete probabilistic model class for stating end-to-end expected-cost theorems on `Unisono.Spec.Objectives`. | [`lean/Unisono/Spec/Models/StochasticWorld.lean`](lean/Unisono/Spec/Models/StochasticWorld.lean) |
| `GenerativeWorld` | Probabilistic full-world with a prior (a family of laws) | A solution is told the hosts, which speakers are outputs of one audio device, the settings of the devices and of the application (nominal rate, block size, request lead, target latency) and one number of the prior, the shape $\alpha$; the weights of the cost are known to it as well. Drawn at random, all independently: each pair's split of its least round-trip time between the two directions (Beta law with both parameters $\alpha$, so both least delays are positive), each clock's offset (uniform), mean rate (log-normal) and wander (stationary Gaussian with exponentially falling covariance), the mean rate and the wander of the clock of each audio device, with the same laws, the error of the timestamps that each audio device reports (stationary Gaussian with mean zero), and the pauses of each directed link and of each host (a pause is a stretch of time in which the link or the host passes nothing; pauses begin at the instants of a Poisson process, a message waits for the backlog of the sending host, of the link and of the receiving host, and a host handles the handovers and the requests of its audio devices after its backlog, so that a request that waits longer than the request lead loses output samples). Not told, to be estimated by a solution: least round-trip times, the rate of the pauses of each link and of each host and the law of their lengths, which may be any law of positive lengths with a mean, the spread and stability of the rates of the clocks of hosts and of audio devices, the size and the correlation time of the error of each device's timestamps, and the range of offsets. Each audio device runs on a clock of its own; no message is lost. | Gives the world a probability law, so that expected cost is a number and optimality (`OptimalWithin` in `lean/Unisono/Spec/Optimality.lean`) can be stated; estimating everything a solution is not told is part of the problem. Its limitations (pauses that do not cluster, independent pairs, constant least delays, device timestamps that are never grossly wrong, no loss) are listed in `docs/specification.tex`. | [`lean/Unisono/Spec/Models/GenerativeWorld.lean`](lean/Unisono/Spec/Models/GenerativeWorld.lean) |

Supplementary component and centralized/oracle analyses live in
`lean/Unisono/Model/` and `lean/Unisono/Analysis/` (`Estimation.lean`,
`Level.lean`, `ModalControl.lean`, `Spectral.lean`); each states its
simplified setting explicitly and supplements, rather than replaces, proofs in
`Unisono.Spec` under the six approved models above.

Some results hold in a sub-case of `GenerativeWorld`. A sub-case is not a
model of its own, and a result in a sub-case does not make a solution
optimal.

| Sub-case | What it assumes | File |
|---|---|---|
| `GenerativeWorld.Member.Noiseless` | A member in which links and hosts never pause, no clock of a host or of an audio device wanders or has a spread of its mean rate, and the audio devices report exact timestamps: every disturbance is switched off. | `lean/Unisono/Spec/Models/GenerativeNoiseless.lean` |
| `GenerativeWorld.Member.SteadyClocks` | A member in which no clock of a host or of an audio device wanders and the audio devices report exact timestamps. Its links and its hosts may pause, with any laws of the lengths, and the mean rates of its clocks may be spread. | `lean/Unisono/Spec/Models/GenerativePauses.lean` |
| `GenerativeWorld.Member.SteadyHosts` | A member with steady clocks whose hosts never pause, so that every host handles the events of its audio devices when they occur. Its links may pause, with any laws of the lengths, and the mean rates of its clocks may be spread. Almost every outcome of such a member is in `ConstantRates`. | `lean/Unisono/Spec/Models/GenerativePauses.lean` |
| `GenerativeWorld.ConstantRates` | An outcome in which no clock of a host or of an audio device wanders, the audio devices report exact timestamps and no host pauses. The clocks may run at different constant rates, and links may pause. | `lean/Unisono/Spec/Models/GenerativeRates.lean` |
| `GenerativeWorld.ConstantDelays` | `ConstantRates` with no pauses, so that every message takes the least delay of its direction. | `lean/Unisono/Spec/Models/GenerativeRates.lean` |

## Layout

| Path | Content |
|---|---|
| `crates/unisono-core` | The pure core: packet codecs, sender, receiver, unified Peer/Star sync (`sync.rs`, `min_rtt.rs`, `kalman.rs`, `blue.rs`), modal regulator (`player.rs`); no I/O, no allocation, nothing that can panic |
| `crates/unisono-dsp` | Signal processing: the resampler that corrects clock drift, sample formats, fades, and gap concealment |
| `crates/unisono-metrics` | Wait-free counters, gauges, and histograms for real-time threads, and their export in the Prometheus text format |
| `crates/unisono-runtime` | Sender and receiver threads around the core: UDP sockets with kernel timestamps, clocks, lock-free SPSC rings, retransmission tracking (`retransmission.rs`), adaptive latency selection (`level.rs`), and virtual devices (`virtual_device.rs`) |
| `crates/unisono-pipewire` | Capture and playback through PipeWire |
| `crates/unisono-alsa` | Capture and playback on an ALSA device |
| `crates/unisono` | The command-line program, including Prometheus metrics export (`src/metrics.rs`) |
| `crates/unisono-c` | A library and C header (`include/unisono.h`) for programs written in C |
| `crates/unisono-sim` | Deterministic true-time simulation of clocks, devices, and links for testing without hardware |
| `crates/translation-check` | Prints inputs and results of `unisono-core` functions to compare against the Lean translation |
| `crates/reachable`, `crates/cycle-cost` | Inspection of the machine code of real-time threads and worst-case cycle instruction counts |
| `lean/UnisonoCore` | Lean translation of `crates/unisono-core`, generated on demand by `just translate` (gitignored) |
| `lean/Unisono` | Formal specification (`Spec/`, `Spec/Models/`, `Spec/Limits.lean`), production-core `Solution` composition (`Solutions/Core.lean`), code-correctness proofs, and supplementary component/oracle analyses (`Analysis/`, `Model/`) |
| `lean/TranslationCheck.lean` | Evaluates the Lean translation on the inputs printed by `translation-check` and checks agreement with Rust |
| `containers` | Containers with PipeWire and ALSA for tests against real audio systems |
| `docs` | Formal specification (`specification.tex`), theorem index (`theorems.md`), wire protocol (`protocol.md`), gap concealment, real-time path, and core Rust subset |
| `tools` | Scripts that fetch and run Aeneas, the audio test containers, and machine-code inspection |

## Checking

`just check` runs what continuous integration runs:

1. formatting, lints and tests of the Rust;
2. compilation for every target platform;
3. an inspection of the machine code of the functions that run on real-time
   threads: it must not enter the kernel, call an allocator, or be able to
   panic;
4. generating the Lean translation of the core (`lean/UnisonoCore/{Types,Funs}.lean`, gitignored);
5. the proofs;
6. the comparison of the translation with the Rust on the same inputs.

It needs [rustup](https://rustup.rs), [just](https://just.systems),
[elan](https://github.com/leanprover/elan) and, for the proofs,
[opam](https://opam.ocaml.org). The first run builds Aeneas and its Lean
library, which takes a while; later runs reuse the cached build and take about a
minute.

`just prove` automatically regenerates the translation whenever
`crates/unisono-core` changes (`just translate` runs only the translation step).

## How the proofs relate to the Rust

A theorem in `lean/Unisono` is about a function in `lean/UnisonoCore`. It
says something about the Rust to the extent that the translation is faithful,
and three things support that:

- `lean/UnisonoCore/{Types,Funs}.lean` are generated directly from
  `crates/unisono-core` before every proof build rather than checked in, so the
  translation cannot go stale;
- a function of the standard library without a Lean model fails the
  translation, so none enters the proofs as an axiom, and
  `lean/Unisono/Audit.lean` pins the axioms each theorem uses;
- every translated function is evaluated in Lean on the inputs the Rust was run
  on, and the results must agree.

## Licence

[Mozilla Public License 2.0](LICENSE).
