// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The system calls that a network thread may make.
//!
//! A network thread reads bytes that anyone who reaches the socket can send.
//! It parses them with the core's parsers, which are proved to return for
//! every input, and what it does with them is little: it receives and sends
//! on a socket that is open already, reads the clock, waits, and writes a
//! line when something is wrong. The kernel can hold a thread to such a
//! list. [`restrict`] asks it to: from then on a system call of the calling
//! thread that is not on the list fails as not permitted (or ends the process
//! on `brk`, because glibc treats an `EPERM` from `brk` as a break address
//! and livelocks on `SIGSEGV`). Opening a file, making a socket, starting a
//! program and changing what memory may be executed are not on the list.
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

    /// The calls of a network thread: receiving and sending on its socket,
    /// waiting for it, reading the clock and sleeping, waking and waiting for
    /// other threads, writing to a file that is open, returning memory, and
    /// what a thread does when it ends.
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
        install(&filter(ALLOWED))
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

    /// The filter that lets the calls in `allowed` through, kills the process
    /// on `SYS_brk` or a foreign architecture, and makes every other call fail
    /// with `EPERM`.
    fn filter(allowed: &[libc::c_long]) -> Vec<libc::sock_filter> {
        // Offsets of `nr` and `arch` in `struct seccomp_data`.
        const NUMBER: u32 = 0;
        const MACHINE: u32 = 4;
        debug_assert!(allowed.len() < usize::from(u8::MAX));
        let load = libc::BPF_LD | libc::BPF_W | libc::BPF_ABS;
        let equal = libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K;
        let answer = libc::BPF_RET | libc::BPF_K;
        // The denial carries the error that the call fails with.
        #[allow(clippy::cast_sign_loss)]
        let denied = libc::SECCOMP_RET_ERRNO | (libc::EPERM as u32 & libc::SECCOMP_RET_DATA);
        // `brk(2)` returns an unsigned address, never `-errno`: returning
        // `EPERM` makes glibc write unmapped memory and livelock in a
        // `SIGSEGV` loop, so `SYS_brk` terminates the process immediately.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let brk_nr = libc::SYS_brk as u32;
        let mut program = vec![
            instruction(load, 0, 0, MACHINE),
            instruction(equal, 1, 0, PROCESSOR),
            instruction(answer, 0, 0, libc::SECCOMP_RET_KILL_PROCESS),
            instruction(load, 0, 0, NUMBER),
            instruction(equal, 0, 1, brk_nr),
            instruction(answer, 0, 0, libc::SECCOMP_RET_KILL_PROCESS),
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

        /// Interprets the generated BPF filter on `(arch, nr)` to verify every
        /// jump offset and verdict without killing the test process.
        fn evaluate(program: &[libc::sock_filter], arch: u32, nr: u32) -> u32 {
            let load = u16::try_from(libc::BPF_LD | libc::BPF_W | libc::BPF_ABS).expect("opcode");
            let equal = u16::try_from(libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K).expect("opcode");
            let answer = u16::try_from(libc::BPF_RET | libc::BPF_K).expect("opcode");
            let mut pc = 0usize;
            let mut acc = 0u32;
            loop {
                let insn = program[pc];
                if insn.code == load {
                    acc = match insn.k {
                        0 => nr,
                        4 => arch,
                        other => panic!("unexpected load offset {other}"),
                    };
                    pc += 1;
                } else if insn.code == equal {
                    let skip = if acc == insn.k { insn.jt } else { insn.jf };
                    pc += 1 + usize::from(skip);
                } else if insn.code == answer {
                    return insn.k;
                } else {
                    panic!("unexpected opcode {}", insn.code);
                }
            }
        }

        #[test]
        fn filter_allows_list_kills_brk_and_wrong_arch_and_denies_other() {
            let program = filter(ALLOWED);
            #[allow(clippy::cast_sign_loss)]
            let eperm = libc::SECCOMP_RET_ERRNO | (libc::EPERM as u32 & libc::SECCOMP_RET_DATA);
            // Wrong architecture kills immediately.
            assert_eq!(
                evaluate(&program, PROCESSOR ^ 1, 0),
                libc::SECCOMP_RET_KILL_PROCESS
            );
            // `SYS_brk` kills immediately instead of returning EPERM.
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let brk_nr = libc::SYS_brk as u32;
            assert_eq!(
                evaluate(&program, PROCESSOR, brk_nr),
                libc::SECCOMP_RET_KILL_PROCESS
            );
            // Every listed syscall is allowed.
            for &call in ALLOWED {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let nr = call as u32;
                assert_eq!(
                    evaluate(&program, PROCESSOR, nr),
                    libc::SECCOMP_RET_ALLOW,
                    "syscall {nr}"
                );
            }
            // Disallowed syscalls like `openat` and `socket` fail with EPERM.
            for call in [libc::SYS_openat, libc::SYS_socket, libc::SYS_close] {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let nr = call as u32;
                assert_eq!(evaluate(&program, PROCESSOR, nr), eperm, "syscall {nr}");
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
