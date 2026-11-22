# Design Principles

**One framework for the whole problem.**
The specification defines the problem once, in both prose and Lean: the world, the observations and actions available to each node, and the objectives. Assumptions about the world, such as bounded delays or second-order noise, are expressed as models within that framework, and every result states which model it assumes. Estimation and control are part of a single solution and are evaluated together, end to end, against the specification's objectives.

*Why:* Results proved in separate models do not compose. A controller that is optimal for a single speaker relative to its own estimate guarantees nothing about synchronization across speakers. Likewise, an estimator's accuracy under a standalone noise model does not determine what a listener hears unless both the estimator and controller are analyzed in the same model against the same objectives. Using a single framework lets results build on each other, keeps every precondition explicit, and shows which questions remain open.

**What a node knows is part of the problem.**
A node acts only on information available to it locally: its own clock, its own audio device, the messages it actually receives (with their delays and losses), and settings fixed in advance. The specification's solution type enforces this constraint in Lean, and the simulator and all analyses follow the same rule. Centralized and oracle designs remain useful as benchmarks because they set limits that no real system can beat, and their numbers are always labeled as such.

*Why:* Giving a node information it cannot have makes a design appear better than it can be in practice, without that advantage being obvious in the final numbers. An instantaneous average across all receivers, a central solver with access to every link, or the simulator's true noise parameters all improve measured performance, yet none of them is available on a real network. Including information constraints in the problem statement keeps these approaches separated as benchmarks rather than allowing them to distort evaluations of real designs.

**One implementation of each algorithm, in the production code.**
Each algorithm has a single Rust implementation in the production core. Lean may have a separate implementation written from scratch as a twin that is easier to reason about. Aeneas, the Rust-to-Lean translator, translates the Rust code into Lean, and we prove the translated code equivalent to the Lean twin, proving that the Rust implementation matches the algorithm. Because the two are proved equivalent, theorems about the Lean twin apply directly to the production code.

*Why:* Separate implementations of the same algorithm drift apart as code changes. Once they diverge, a property proved or measured on one no longer applies to the other. Maintaining a second implementation is justified only when a proof links it to the production code.

**The simulator is a world, not a second system.**
The simulator models clocks, devices, links, and their failures. It drives the production code through the same interfaces that the runtime uses and evaluates the specification's objectives using true time. It implements no estimators or controllers of its own.

*Why:* If the simulator implements its own algorithms, benchmarks measure those algorithms rather than the production system. Driving the production code makes every benchmark a test of the actual product. The same scenarios can then serve as regression tests, and recorded traces from real systems can later replace parts of the simulated environment.

**Every claim names its evidence and its assumptions.**
The terms "optimal", "proved", and "verified" refer strictly to a theorem in the framework under a named model. In particular, optimality must always refer to the objectives in the single problem definition and nothing else, so that it cannot mislead. Empirical numbers must come from a reproducible run and report both the configuration used and their spread across random seeds. When a result depends on a parameter that a node cannot know, it must also show how the result changes when that parameter is wrong. The complete list of sets of assumptions (i.e. models) must be maintained up to date in the README, each with an unambiguous name, short description, and motivation.

*Why:* Overstating a result wastes more effort than it saves: someone eventually has to find and correct the error, and until then it misleads every decision based on it. Calling something "optimal" without complete agreement on the objectives and setting is deceitful. When a claim cites its theorem or run along with its assumptions, anyone can verify it and understand its limits before relying on it.
