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
    its host and the delay back. The theorem assumes that no two messages
    from different hosts arrive at one host at the same time, and zero
    weights on latency and roughness.
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
  - A star solution's costs in a world and in the same world with the links
    to and from the sender shifted add up to at least twice the cost of half
    the shift (`lean/Unisono/Spec/StarShift.lean`), for any number of hosts.
  - The baseline is optimal among star solutions within a known margin
    (`Unisono.Solutions.FixedDelay.optimalWithin` in
    `lean/Unisono/Solutions/FixedDelay/Optimal.lean`). A star solution is one
    whose hosts exchange messages only with the sender. The theorem is
    stated for every member of `GenerativeWorld`, with the margin `⊤` for
    every member that it does not cover. In every noiseless member within
    the baseline's delivery margin, with any number of hosts and speakers,
    the expected cost of `Unisono.Solutions.FixedDelay` exceeds that of no
    compared star solution (`GenerativeWorld.StarSolutions`) by more than the sum of the weights of
    synchronization and tracking times `ρ³ / (4 Θ)`, where `ρ` is the sum
    over the speakers of the least round-trip time between the sender and the
    speaker's host and `Θ` bounds the clock offsets. The theorem needs zero
    weights on latency and roughness and no speaker on the sender's host.
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
  - No solution is proved optimal among all solutions under `GenerativeWorld`.
    The proved optimality compares only solutions whose hosts exchange
    messages with the sender alone, in noiseless members; with two or more
    receiving hosts, a solution that also uses links between them can do
    better. No lower bound on expected cost is proved for such solutions, or
    for members with pauses or clock wander.
    Random worlds are constructed for every noiseless member and for one
    member with random mean clock rates; random worlds with pauses or
    with clock wander are not yet constructed in Lean. The expectation that a solution loses nothing in the long run by
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
| Capture device | $c(n), f(b), h(b), \hat c(b)$ (`World.source`) | True capture time $c(n)$ of frame $n$, first frame $f(b)$ of block $b$, handoff time $h(b)$ to the sender host, and reported host-clock timestamp $\hat c(b)$ (subject to timestamp error). |
| Playback devices (speakers) | $o_r(k), g_r(b), a_r(b), \hat o_r(b)$ (`World.speaker`) | True output time $o_r(k)$ of sample $k$ on speaker $r$, first sample $g_r(b)$ of block $b$, request time $a_r(b)$ to the host (request lead $o_r(g_r(b)) - a_r(b)$), and reported host-clock timestamp $\hat o_r(b)$. |
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
| `GenerativeWorld` | Probabilistic full-world with a prior (a family of laws) | A solution is told the hosts, which speakers are outputs of one audio device, the settings of the devices and of the application (nominal rate, block size, request lead, target latency) and one number of the prior, the shape $\alpha$; the weights of the cost are known to it as well. Drawn at random, all independently: each pair's split of its least round-trip time between the two directions (Beta law with both parameters $\alpha$, so both least delays are positive), each clock's offset (uniform), mean rate (log-normal) and wander (stationary Gaussian with exponentially falling covariance), the mean rate and the wander of the clock of each audio device, with the same laws, the error of the timestamps that each audio device reports (stationary Gaussian with mean zero), and the pauses of each directed link and of each host (a pause is a stretch of time in which the link or the host passes nothing; pauses begin at the instants of a Poisson process, and a message waits for the backlog of the sending host, of the link and of the receiving host). Not told, to be estimated by a solution: least round-trip times, the rate of the pauses of each link and of each host and the law of their lengths, which may be any law of positive lengths with a mean, the spread and stability of the rates of the clocks of hosts and of audio devices, the size and the correlation time of the error of each device's timestamps, and the range of offsets. Each audio device runs on a clock of its own; no message is lost. | Gives the world a probability law, so that expected cost is a number and optimality (`OptimalWithin` in `lean/Unisono/Spec/Optimality.lean`) can be stated; estimating everything a solution is not told is part of the problem. Its limitations (pauses that do not cluster, independent pairs, constant least delays, device timestamps that are never grossly wrong, no loss) are listed in `docs/specification.tex`. | [`lean/Unisono/Spec/Models/GenerativeWorld.lean`](lean/Unisono/Spec/Models/GenerativeWorld.lean) |

Supplementary component and centralized/oracle analyses live in
`lean/Unisono/Model/` and `lean/Unisono/Analysis/` (`Estimation.lean`,
`Level.lean`, `ModalControl.lean`, `Spectral.lean`); each states its
simplified setting explicitly and supplements, rather than replaces, proofs in
`Unisono.Spec` under the six approved models above.

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
