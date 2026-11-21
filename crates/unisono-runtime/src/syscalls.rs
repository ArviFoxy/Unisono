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
//! thread that is not on the list fails, as one that is not permitted, and
//! does nothing. Opening a file, making a socket, starting a program and
//! changing what memory may be executed are not on the list.
//!
//! The list belongs to the thread that asks and to the threads it starts
//! later, not to the threads that run already. It cannot be taken back.

use std::io;

/// The calls of a network thread: receiving and sending on its socket,
/// waiting for it, reading the clock and sleeping, waking and waiting for
/// other threads, writing to a file that is open, returning memory, and
/// what a thread does when it ends.
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
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
/// number of the processor in the format of programs, with the marks for 64
/// bits and for the low byte first.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const PROCESSOR: u32 = 0xc000_003e;
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const PROCESSOR: u32 = 0xc000_00b7;

/// Holds the calling thread to the system calls of a network thread.
///
/// # Errors
///
/// What the system says when it does not take the list, and that this is
/// not done on other systems and processors than Linux on x86-64 and on
/// 64-bit ARM. The thread then runs on as it was.
pub fn restrict() -> io::Result<()> {
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    {
        install(&filter(ALLOWED))
    }
    #[cfg(not(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    )))]
    {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "system calls are restricted on Linux on x86-64 and 64-bit ARM only",
        ))
    }
}

/// One instruction of the kernel's filter machine.
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
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

/// The filter that lets the calls in `allowed` through and makes every
/// other call fail as not permitted. A call made in the manner of another
/// processor, which numbers its calls differently, ends the program.
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn filter(allowed: &[libc::c_long]) -> Vec<libc::sock_filter> {
    // Where the kernel puts the number of the call and the processor in
    // what the filter reads.
    const NUMBER: u32 = 0;
    const MACHINE: u32 = 4;
    let load = libc::BPF_LD | libc::BPF_W | libc::BPF_ABS;
    let equal = libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K;
    let answer = libc::BPF_RET | libc::BPF_K;
    // The denial carries the error that the call fails with.
    #[allow(clippy::cast_sign_loss)]
    let denied = libc::SECCOMP_RET_ERRNO | (libc::EPERM as u32 & libc::SECCOMP_RET_DATA);
    let mut program = vec![
        instruction(load, 0, 0, MACHINE),
        instruction(equal, 1, 0, PROCESSOR),
        instruction(answer, 0, 0, libc::SECCOMP_RET_KILL_PROCESS),
        instruction(load, 0, 0, NUMBER),
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
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn install(program: &[libc::sock_filter]) -> io::Result<()> {
    let length = u16::try_from(program.len())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "the filter is too long"))?;
    let handed = libc::sock_fprog {
        len: length,
        filter: program.as_ptr().cast_mut(),
    };
    // A thread may restrict itself without a privilege only when it also
    // gives up gaining privileges by starting a program.
    // SAFETY: `prctl` with these arguments reads numbers only.
    let gave_up = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
    if gave_up != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: `handed` points to `program`, which lives through the call;
    // the kernel copies the filter and keeps no pointer.
    let taken = unsafe {
        libc::prctl(
            libc::PR_SET_SECCOMP,
            libc::SECCOMP_MODE_FILTER,
            std::ptr::from_ref(&handed),
        )
    };
    if taken == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64", not(loom)))]
mod tests {
    use std::net::UdpSocket;
    use std::time::Duration;

    use super::restrict;
    use crate::clock;

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
        });
        let mut bytes = [0u8; 16];
        let (length, _) = there.recv_from(&mut bytes).expect("receiving");
        assert_eq!(&bytes[..length], b"unisono");
        thread.join().expect("the thread ends");
        // The thread that asked is restricted, and no other.
        std::fs::File::open("/dev/null").expect("this thread opens files");
    }
}
