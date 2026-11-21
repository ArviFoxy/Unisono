// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The system calls that a network thread may make.
//!
//! A network thread reads bytes that anyone who reaches the socket can send.
//! It parses them with the core's parsers, which are proved to return for
//! every input, and what it does with them is little: it receives and sends
//! on a socket that is open already, reads the clock, waits, writes a line
//! when something is wrong, manages non-executable memory (`brk`, `munmap`,
//! `madvise`, and `mmap`/`mprotect` without `PROT_EXEC`) so allocator teardown
//! on thread exit cannot fail or livelock, and signals its own process via
//! `tgkill` so `abort()` terminates cleanly. Opening a file, making a socket,
//! starting a program and making memory executable are not on the list.
//!
//! The list belongs to the thread that asks and to the threads it starts
//! later, not to the threads that run already. It cannot be taken back.

use std::io;

/// Holds the calling thread to the system calls of a network thread.
///
/// # Errors
///
/// What the system says when it does not take the list, and `Unsupported` on
/// systems and processors other than little-endian Linux on x86-64 and
/// 64-bit ARM. The thread then runs on as it was.
pub fn restrict() -> io::Result<()> {
    #[cfg(all(
        target_os = "linux",
        target_endian = "little",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    {
        linux::restrict()
    }
    #[cfg(not(all(
        target_os = "linux",
        target_endian = "little",
        any(target_arch = "x86_64", target_arch = "aarch64")
    )))]
    {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "system calls are restricted on little-endian Linux on x86-64 and 64-bit ARM only",
        ))
    }
}

#[cfg(all(
    target_os = "linux",
    target_endian = "little",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
mod linux {
    use std::io;

    /// The calls of a network thread that are allowed unconditionally:
    /// receiving and sending on its socket, waiting for it, reading the clock
    /// and sleeping, waking and waiting for other threads, writing to a file
    /// that is open, heap/memory management without making pages executable,
    /// and what a thread does when it ends.
    ///
    /// `mmap`, `mprotect` (only without `PROT_EXEC`) and `tgkill` (only for
    /// this process's own PID) are checked with argument filters in [`filter`].
    const ALLOWED: &[libc::c_long] = &[
        libc::SYS_recvmsg,
        libc::SYS_recvfrom,
        libc::SYS_recvmmsg,
        libc::SYS_sendto,
        libc::SYS_sendmsg,
        libc::SYS_sendmmsg,
        #[cfg(target_arch = "x86_64")]
        libc::SYS_poll,
        libc::SYS_ppoll,
        libc::SYS_clock_gettime,
        libc::SYS_clock_nanosleep,
        libc::SYS_nanosleep,
        libc::SYS_sched_yield,
        libc::SYS_futex,
        libc::SYS_write,
        libc::SYS_brk,
        libc::SYS_munmap,
        libc::SYS_madvise,
        libc::SYS_rt_sigprocmask,
        libc::SYS_rt_sigreturn,
        libc::SYS_sigaltstack,
        libc::SYS_restart_syscall,
        libc::SYS_exit,
        libc::SYS_exit_group,
    ];

    /// How the kernel names the processor whose calls the list is for: the
    /// number of the processor in the format of programs, with the marks for
    /// 64 bits (`__AUDIT_ARCH_64BIT`) and little-endian (`__AUDIT_ARCH_LE`).
    #[cfg(target_arch = "x86_64")]
    const PROCESSOR: u32 = 0xc000_003e;
    #[cfg(target_arch = "aarch64")]
    const PROCESSOR: u32 = 0xc000_00b7;

    /// Restricts the calling thread with the BPF program built from `ALLOWED`.
    pub(super) fn restrict() -> io::Result<()> {
        // SAFETY: `getpid` is always safe and returns the current process ID.
        let pid = u32::try_from(unsafe { libc::getpid() })
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "process id is negative"))?;
        install(&filter(ALLOWED, pid))
    }

    /// One instruction of the kernel's filter machine.
    fn instruction(code: u32, yes: u8, no: u8, value: u32) -> libc::sock_filter {
        libc::sock_filter {
            // The codes of the filter machine fit in 16 bits.
            #[allow(clippy::cast_possible_truncation)]
            code: code as u16,
            jt: yes,
            jf: no,
            k: value,
        }
    }

    /// The filter that kills the process on a foreign architecture, allows
    /// `mmap`/`mprotect` without `PROT_EXEC`, allows `tgkill` for `pid` only,
    /// allows the calls in `allowed`, and fails every other call with `EPERM`.
    fn filter(allowed: &[libc::c_long], pid: u32) -> Vec<libc::sock_filter> {
        // Offsets in little-endian `struct seccomp_data`:
        //   0: nr (u32), 4: arch (u32), 8: ip (u64),
        //  16: args[0] (u64 -> lo=16, hi=20),
        //  32: args[2] (u64 -> lo=32, hi=36).
        const NUMBER: u32 = 0;
        const MACHINE: u32 = 4;
        const ARG0_LO: u32 = 16;
        const ARG0_HI: u32 = 20;
        const ARG2_LO: u32 = 32;
        debug_assert!(allowed.len() < usize::from(u8::MAX));
        let load = libc::BPF_LD | libc::BPF_W | libc::BPF_ABS;
        let equal = libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K;
        let bitset = libc::BPF_JMP | libc::BPF_JSET | libc::BPF_K;
        let answer = libc::BPF_RET | libc::BPF_K;
        // The denial carries the error that the call fails with.
        #[allow(clippy::cast_sign_loss)]
        let denied = libc::SECCOMP_RET_ERRNO | (libc::EPERM as u32 & libc::SECCOMP_RET_DATA);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let mmap_nr = libc::SYS_mmap as u32;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let mprotect_nr = libc::SYS_mprotect as u32;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let tgkill_nr = libc::SYS_tgkill as u32;
        #[allow(clippy::cast_sign_loss)]
        let prot_exec = libc::PROT_EXEC as u32;

        let mut program = vec![
            // 0..=2: verify architecture, killing on foreign ABI.
            instruction(load, 0, 0, MACHINE),
            instruction(equal, 1, 0, PROCESSOR),
            instruction(answer, 0, 0, libc::SECCOMP_RET_KILL_PROCESS),
            // 3: load syscall number.
            instruction(load, 0, 0, NUMBER),
            // 4..=9: allow `mmap` and `mprotect` only when `PROT_EXEC` is clear.
            instruction(equal, 1, 0, mmap_nr),
            instruction(equal, 0, 4, mprotect_nr),
            instruction(load, 0, 0, ARG2_LO),
            instruction(bitset, 1, 0, prot_exec),
            instruction(answer, 0, 0, libc::SECCOMP_RET_ALLOW),
            instruction(answer, 0, 0, denied),
            // 10..=16: allow `tgkill` only targeting this process's own PID.
            instruction(equal, 0, 6, tgkill_nr),
            instruction(load, 0, 0, ARG0_HI),
            instruction(equal, 0, 3, 0),
            instruction(load, 0, 0, ARG0_LO),
            instruction(equal, 0, 1, pid),
            instruction(answer, 0, 0, libc::SECCOMP_RET_ALLOW),
            instruction(answer, 0, 0, denied),
        ];
        for (place, &call) in allowed.iter().enumerate() {
            // Past the comparisons that remain and the denial. The list has far
            // fewer than 256 calls, and their numbers are small and positive.
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            program.push(instruction(
                equal,
                (allowed.len() - place) as u8,
                0,
                call as u32,
            ));
        }
        program.push(instruction(answer, 0, 0, denied));
        program.push(instruction(answer, 0, 0, libc::SECCOMP_RET_ALLOW));
        program
    }

    /// Hands `program` to the kernel for the calling thread.
    fn install(program: &[libc::sock_filter]) -> io::Result<()> {
        let length = u16::try_from(program.len())
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "the filter is too long"))?;
        let handed = libc::sock_fprog {
            len: length,
            filter: program.as_ptr().cast_mut(),
        };
        // A thread may restrict itself without a privilege only when it also
        // gives up gaining privileges by starting a program.
        // SAFETY: `prctl` is variadic with 5 arguments; passing all 5 with
        // `c_ulong` types matches the Linux syscall ABI.
        let gave_up = unsafe {
            libc::prctl(
                libc::PR_SET_NO_NEW_PRIVS,
                1 as libc::c_ulong,
                0 as libc::c_ulong,
                0 as libc::c_ulong,
                0 as libc::c_ulong,
            )
        };
        if gave_up != 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: `handed` points to `program`, which lives through the call;
        // the kernel copies the filter and keeps no pointer. All 5 variadic
        // arguments are supplied with `c_ulong` types.
        #[allow(clippy::cast_lossless, clippy::cast_sign_loss)]
        let taken = unsafe {
            libc::prctl(
                libc::PR_SET_SECCOMP,
                libc::SECCOMP_MODE_FILTER as libc::c_ulong,
                std::ptr::from_ref(&handed) as usize as libc::c_ulong,
                0 as libc::c_ulong,
                0 as libc::c_ulong,
            )
        };
        if taken == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    #[cfg(all(test, not(loom)))]
    mod tests {
        use std::net::UdpSocket;
        use std::time::Duration;

        use super::{ALLOWED, PROCESSOR, filter, restrict};
        use crate::clock;

        /// Interprets the generated BPF filter on `(arch, nr, args)` to verify
        /// every jump offset and verdict without killing the test process.
        fn evaluate(program: &[libc::sock_filter], arch: u32, nr: u32, args: [u64; 6]) -> u32 {
            let load = u16::try_from(libc::BPF_LD | libc::BPF_W | libc::BPF_ABS).expect("opcode");
            let equal = u16::try_from(libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K).expect("opcode");
            let bitset =
                u16::try_from(libc::BPF_JMP | libc::BPF_JSET | libc::BPF_K).expect("opcode");
            let answer = u16::try_from(libc::BPF_RET | libc::BPF_K).expect("opcode");
            let mut pc = 0usize;
            let mut acc = 0u32;
            loop {
                let insn = program[pc];
                if insn.code == load {
                    #[allow(clippy::cast_possible_truncation)]
                    let word = match insn.k {
                        0 => nr,
                        4 => arch,
                        16 => args[0] as u32,
                        20 => (args[0] >> 32) as u32,
                        32 => args[2] as u32,
                        36 => (args[2] >> 32) as u32,
                        other => panic!("unexpected load offset {other}"),
                    };
                    acc = word;
                    pc += 1;
                } else if insn.code == equal {
                    let skip = if acc == insn.k { insn.jt } else { insn.jf };
                    pc += 1 + usize::from(skip);
                } else if insn.code == bitset {
                    let skip = if (acc & insn.k) != 0 {
                        insn.jt
                    } else {
                        insn.jf
                    };
                    pc += 1 + usize::from(skip);
                } else if insn.code == answer {
                    return insn.k;
                } else {
                    panic!("unexpected opcode {}", insn.code);
                }
            }
        }

        #[test]
        fn filter_checks_arch_exec_prot_tgkill_and_allowed_syscalls() {
            let pid = 4242u32;
            let program = filter(ALLOWED, pid);
            #[allow(clippy::cast_sign_loss)]
            let eperm = libc::SECCOMP_RET_ERRNO | (libc::EPERM as u32 & libc::SECCOMP_RET_DATA);
            let zero = [0u64; 6];
            // Wrong architecture kills immediately.
            assert_eq!(
                evaluate(&program, PROCESSOR ^ 1, 0, zero),
                libc::SECCOMP_RET_KILL_PROCESS
            );
            // Every listed syscall (including `SYS_brk`) is allowed.
            for &call in ALLOWED {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let nr = call as u32;
                assert_eq!(
                    evaluate(&program, PROCESSOR, nr, zero),
                    libc::SECCOMP_RET_ALLOW,
                    "syscall {nr}"
                );
            }
            // `mmap` and `mprotect` are allowed without `PROT_EXEC` and denied with it.
            #[allow(clippy::cast_sign_loss)]
            let rw = u64::from((libc::PROT_READ | libc::PROT_WRITE) as u32);
            #[allow(clippy::cast_sign_loss)]
            let rx = u64::from((libc::PROT_READ | libc::PROT_EXEC) as u32);
            for call in [libc::SYS_mmap, libc::SYS_mprotect] {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let nr = call as u32;
                assert_eq!(
                    evaluate(&program, PROCESSOR, nr, [0, 4096, rw, 0, 0, 0]),
                    libc::SECCOMP_RET_ALLOW,
                    "non-exec syscall {nr}"
                );
                assert_eq!(
                    evaluate(&program, PROCESSOR, nr, [0, 4096, rx, 0, 0, 0]),
                    eperm,
                    "exec syscall {nr}"
                );
            }
            // `tgkill` is allowed only for our own PID (with zero high bits).
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let tgkill_nr = libc::SYS_tgkill as u32;
            assert_eq!(
                evaluate(
                    &program,
                    PROCESSOR,
                    tgkill_nr,
                    [u64::from(pid), u64::from(pid), 6, 0, 0, 0]
                ),
                libc::SECCOMP_RET_ALLOW
            );
            assert_eq!(
                evaluate(
                    &program,
                    PROCESSOR,
                    tgkill_nr,
                    [u64::from(pid + 1), u64::from(pid), 6, 0, 0, 0]
                ),
                eperm
            );
            assert_eq!(
                evaluate(
                    &program,
                    PROCESSOR,
                    tgkill_nr,
                    [(1u64 << 32) | u64::from(pid), u64::from(pid), 6, 0, 0, 0]
                ),
                eperm
            );
            // Disallowed syscalls like `openat`, `socket`, and `close` fail with EPERM.
            for call in [libc::SYS_openat, libc::SYS_socket, libc::SYS_close] {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let nr = call as u32;
                assert_eq!(
                    evaluate(&program, PROCESSOR, nr, zero),
                    eperm,
                    "syscall {nr}"
                );
            }
        }

        #[test]
        fn a_restricted_thread_sends_receives_and_ends_but_opens_nothing() {
            let here = UdpSocket::bind("127.0.0.1:0").expect("a socket");
            let there = UdpSocket::bind("127.0.0.1:0").expect("a socket");
            there
                .set_read_timeout(Some(Duration::from_secs(2)))
                .expect("a timeout");
            let to = there.local_addr().expect("an address");
            let thread = std::thread::spawn(move || {
                restrict().expect("the list is taken");
                // What a network thread does goes on.
                here.send_to(b"unisono", to).expect("sending");
                let before = clock::raw();
                std::thread::sleep(Duration::from_millis(2));
                assert!(clock::raw() > before);
                // Non-executable anonymous mmap succeeds, while making it executable fails with EPERM.
                // SAFETY: anonymous mapping of one page, unmapped right after.
                let page = unsafe {
                    libc::mmap(
                        std::ptr::null_mut(),
                        4096,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                        -1,
                        0,
                    )
                };
                assert_ne!(page, libc::MAP_FAILED);
                // SAFETY: `page` is a valid 4096-byte mapping.
                let rc = unsafe { libc::mprotect(page, 4096, libc::PROT_READ | libc::PROT_EXEC) };
                assert_eq!(rc, -1);
                assert_eq!(
                    std::io::Error::last_os_error().raw_os_error(),
                    Some(libc::EPERM)
                );
                // SAFETY: `page` is a valid 4096-byte mapping.
                assert_eq!(unsafe { libc::munmap(page, 4096) }, 0);
                // What it does not do fails, and the thread runs on.
                let opened = std::fs::File::open("/dev/null");
                let error = opened.expect_err("opening a file is not on the list");
                assert_eq!(error.raw_os_error(), Some(libc::EPERM));
                let made = UdpSocket::bind("127.0.0.1:0");
                assert!(made.is_err(), "making a socket is not on the list");
                // Return `here` so `close(fd)` runs outside seccomp.
                here
            });
            let mut bytes = [0u8; 16];
            let (length, _) = there.recv_from(&mut bytes).expect("receiving");
            assert_eq!(&bytes[..length], b"unisono");
            let here = thread.join().expect("the thread ends");
            drop(here);
            // The thread that asked is restricted, and no other.
            std::fs::File::open("/dev/null").expect("this thread opens files");
        }
    }
}
