# The real-time path

Audio is processed on the cycle of a device, and a cycle that takes too long
is heard. This page says what is known about the code that runs there, how it
is known, and what is not known.

## What is checked on every build

`tools/realtime.sh`, which `just check` runs, builds the functions of the core
that are called on real-time threads into one library, links them with
everything they reach and nothing else, and inspects the machine code. The
functions are those that take in a packet, plan a cycle, take and skip frames,
make and take in reports, take in a report of a device and ask its line for a
time or for the start and length of a cycle, and read and write packets. The check fails unless:

- **the code needs nothing from outside but the functions that copy and fill
  memory.** It therefore calls no allocator, takes no lock, and calls no
  library;
- **it contains no instruction that enters the kernel;**
- **it contains none of the machinery of a panic,** so no path through it can
  panic. This is the same fact that the theorems in `lean/Unisono` state about
  the translation of each function: it returns for every state and every
  argument. The library's handler of a panic calls a function that is
  defined nowhere, so a path to a panic that the compiler keeps leaves a
  reference that cannot be resolved, and the check sees it by name. On every
  run the check also builds a function that does panic and fails unless that
  reference appears: the check is seen to catch what it is for;
- **every reached function is audited fail-closed by `crates/reachable`,**
  with jump tables disabled (`-max-jump-table-size=0`), so no direct call,
  unconditional or conditional jump, linear fallthrough, or indirect branch
  can leave unisono's own code or reach a trap or kernel entry.

These are statements about every path, not about the paths that a test ran.
They hold for the code as compiled for the machine that runs the check.

## The audio threads' whole cycles

The core is one part of what an audio thread runs. The rest uses the
standard library: the receiver's playback takes in what the network thread
handed over, plans with the core, resamples, conceals and fades; the
sender's capture hands frames to the network thread. `tools/realtime-audio`
builds the two cycles with runtime-sized slices into a library of their
own, and `crates/reachable` follows every direct call, jump, fallthrough,
and relocation-backed indirect call from them through the demangled machine
code. The check fails unless every function they reach belongs to unisono,
one of the functions that copy and fill memory, or one of the compiler's
helpers for 128-bit arithmetic, and none of them enters the kernel, traps,
or branches through an unresolved pointer.
A path to a panic, to the allocator or to a lock reaches a function of
the standard library and fails it; so does freeing memory. It is seen to
fail: a function with a path to a panic is built beside them, and the
check must reject it.

The check found, when it was first run, paths that panic in the pump (a
division by the number of channels, a copy whose range the compiler could
not bound), in the concealment (copies of slices whose lengths are equal
but not known to be, `clamp` on numbers, which checks its limits), and the
freeing of a buffer on both threads where a full ring would give it back.
All of them are gone; the buffers are kept, never freed, in the case that
cannot happen.

## What the proofs add

Every loop of the core has, in its proof, a quantity that decreases with each
round and cannot go below zero. So every function ends.

For the loops over the frames a receiver holds, over the arrivals it keeps and
over the reports of a device, the number of rounds is a theorem of its own
(`Unisono/Rounds.lean`): marking the frames of a packet takes one round for
each frame, counting held or missing frames one for each frame up to the limit
asked for, moving the playhead one for each frame passed, clearing the stretch
one for each of its words, finding an arrival one for each arrival kept, and
fitting the line of a device one for each report kept. None of these depends
on the state or on what arrived. *The loops of the estimator and of reading
and writing a packet are proved to end; their bounds are not yet stated.*

## What is not known

**How long a cycle takes.** A bound in seconds that holds for every input
needs a model of the processor's timing: its caches, its pipeline and its
prediction of branches. Tools that have such models cover microcontrollers,
not the processors that unisono runs on. Three things stand in for it:

- the bound on the work, above;
- a count of the instructions that a cycle and the taking in of a packet
  execute on the inputs that cost most: a cycle whose frames are all held, a
  cycle in which a gap begins, a cycle inside a gap, a packet, a packet that
  ends a window of the estimator, and a report of a device. The program in
  `crates/cycle-cost` runs each under single-stepping and counts. The count is
  the same on every run, each case has a budget about a quarter above what it
  counted when the budget was set, and `just check` fails when a case goes
  over;
- the time of the same calls on the machine that runs the program, which it
  prints and does not judge.

A count of instructions is not a time: an instruction that misses the cache
costs a hundred that do not. The count catches a change that makes a cycle do
more work; it says nothing about the machine.

**What the processor and the operating system add.** Memory that is not in
place when it is touched, floating-point numbers so small that arithmetic on
them is slow, and interrupts are outside what any of the above sees. The
program locks the memory it has once both its network and audio threads run
and everything they use is made (`unisono_runtime::memory`); its own threads
use 512 KiB stacks to keep locked-memory use modest. Systems that enforce a
low default `RLIMIT_MEMLOCK` (for example 8 MiB) will still refuse `mlockall`
unless raised to roughly 16 MiB for ALSA or 32–64 MiB for PipeWire (due to
shared libraries and PipeWire's IPC/shared-memory pools); failure to lock
memory is warned on stderr and does not abort the process. The only
recurrence on the audio path, the concealment's prediction, takes a value
too small for full precision as silence, so such numbers do not arise there;
the processor is not set to treat them as zero. Interrupts and the
scheduler are the system's: the thread of an ALSA device asks the system to
schedule it ahead of ordinary threads and says whether it does
(`unisono_alsa::Running::realtime`), and PipeWire schedules the thread of its
graph itself.

**The network thread.** It enters the kernel by its nature, and it reads
bytes that anyone who reaches its socket can send. The kernel holds it to a
list of system calls (`unisono_runtime::syscalls`): receiving and sending on
the socket that is open, waiting for it, reading the clock and sleeping,
waking other threads, writing to a file that is open, returning memory, and
ending. Any other call of that thread fails as not permitted and does
nothing: it cannot open a file, make a socket, start a program or change
what memory may be executed. The program asks for this at the start of the
network thread of a sender and of a receiver, on Linux on x86-64 and 64-bit
ARM; elsewhere the thread runs unrestricted and a line says so. A test
holds a thread to the list and has it send, sleep and end, and fail to open
a file and to make a socket.
