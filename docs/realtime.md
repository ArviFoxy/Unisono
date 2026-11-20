# The real-time path

Audio is processed on the cycle of a device, and a cycle that takes too long
is heard. This page says what is known about the code that runs there, how it
is known, and what is not known.

## What is checked on every build

`tools/realtime.sh`, which `just check` runs, builds the functions of the core
that are called on real-time threads into one library, links them with
everything they reach and nothing else, and inspects the machine code. The
functions are those that take in a packet, plan a cycle, take and skip frames,
make and take in reports, fit the line of a device, and read and write
packets. The check fails unless:

- **the code needs nothing from outside but the functions that copy and fill
  memory.** It therefore calls no allocator, takes no lock, and calls no
  library;
- **it contains no instruction that enters the kernel;**
- **it contains none of the machinery of a panic,** so no path through it can
  panic. This is the same fact that the theorems in `lean/Unisono` state about
  the translation of each function: it returns for every state and every
  argument;
- **the sources of the core have no trait object and no pointer to a
  function,** so every call is to a function the compiler knows, and the code
  that was inspected is all the code these functions can run.

These are statements about every path, not about the paths that a test ran.
They hold for the code as compiled for the machine that runs the check.

## What the proofs add

Every loop of the core has, in its proof, a quantity that decreases with each
round and cannot go below zero. So every function ends, and the number of
rounds of each loop is bounded by numbers of the configuration: the frames of
a cycle, the words of the stretch, the samples of an estimate. *The bounds are
not yet stated as theorems of their own.*

## What is not known

**How long a cycle takes.** A bound in seconds that holds for every input
needs a model of the processor's timing: its caches, its pipeline and its
prediction of branches. Tools that have such models cover microcontrollers,
not the processors that unisono runs on. What can be had instead is a bound on
the work, as above, a count of instructions on the inputs that the bound shows
to be the worst, which is the same on every run and can be held against a
budget, and measurement on the machine that is used. *None of the three is
built.*

**The code outside the core.** The resampler, the concealment and the code
that turns a plan into frames use floating point and slices. They are tested
not to allocate, but their machine code is not inspected yet, and they may
hold paths that panic. The thread that reads and writes the network has to
enter the kernel; for it the kernel can be made to enforce a list of the
system calls it may make. *Not built.*

**What the processor and the operating system add.** Memory that is not in
place when it is touched, floating-point numbers so small that arithmetic on
them is slow, and interrupts are outside what any of the above sees. The
runtime is to lock and touch its memory before it starts and to make the
processor treat such numbers as zero on its real-time threads. *Not built.*
