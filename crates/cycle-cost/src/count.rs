// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Deterministic user-space instruction counting via `ptrace` single-stepping.
//!
//! Executes the target closure in a child process and counts user-space
//! instructions step by step; for pure deterministic code without I/O or
//! clock reads, the count is reproducible across runs.

use std::io;

/// The number of instructions that `work` executes.
///
/// # Errors
///
/// When the operating system does not let this process trace a child of its
/// own, when the work ends in another way than by returning, and on every
/// system but Linux.
pub(crate) fn instructions(work: &mut dyn FnMut()) -> io::Result<u64> {
    #[cfg(target_os = "linux")]
    {
        let around = linux::between_marks(&mut || {})?;
        let with = linux::between_marks(work)?;
        Ok(with.saturating_sub(around))
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = work;
        Err(io::Error::other("instructions are counted on Linux only"))
    }
}

#[cfg(target_os = "linux")]
mod linux {
    use std::ffi::c_void;
    use std::{io, ptr};

    /// Waits for `child` to change state, retrying if a signal interrupts the
    /// wait.
    fn wait_child(child: libc::pid_t) -> io::Result<libc::c_int> {
        let mut status = 0;
        loop {
            // SAFETY: `child` is a child of this process and `status` is a
            // valid pointer to one integer.
            let waited = unsafe { libc::waitpid(child, &raw mut status, 0) };
            if waited != -1 {
                return Ok(status);
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }

    /// Lets the child that waits at a stop run until it stops at the signal
    /// `SIGSTOP` again, one instruction at a time, and returns the number of
    /// instructions it executed.
    fn step_to_stop(child: libc::pid_t) -> io::Result<u64> {
        let mut count = 0u64;
        loop {
            let null = ptr::null_mut::<c_void>();
            // SAFETY: `child` is a child of this process that is stopped under
            // its trace, and the variadic address and data arguments are typed
            // null pointers.
            if unsafe { libc::ptrace(libc::PTRACE_SINGLESTEP, child, null, null) } == -1 {
                return Err(io::Error::last_os_error());
            }
            let status = wait_child(child)?;
            if !libc::WIFSTOPPED(status) {
                return Err(io::Error::other(
                    "the measured work ended before its end was marked",
                ));
            }
            match libc::WSTOPSIG(status) {
                libc::SIGSTOP => return Ok(count),
                libc::SIGTRAP => count += 1,
                signal => {
                    return Err(io::Error::other(format!(
                        "the measured work was stopped by signal {signal}"
                    )));
                }
            }
        }
    }

    /// Ends and reaps `child`, whatever state it is in.
    fn reap(child: libc::pid_t) {
        let mut status = 0;
        // SAFETY: `child` is a child of this process; killing and reaping it
        // leaves no zombie behind.
        unsafe {
            libc::kill(child, libc::SIGKILL);
            while libc::waitpid(child, &raw mut status, 0) == -1
                && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted
            {}
        }
    }

    /// The number of instructions between the two marks in the child, of which
    /// those of `work` are a part: the rest is the end of one mark and the
    /// beginning of the next.
    pub(super) fn between_marks(work: &mut dyn FnMut()) -> io::Result<u64> {
        // SAFETY: the process has one thread, so the child may go on running
        // Rust code after the fork. The child asks to be traced, stops, does the
        // work, stops again and ends without running anything that the parent
        // set up to run at its own end.
        let child = unsafe { libc::fork() };
        if child == -1 {
            return Err(io::Error::last_os_error());
        }
        if child == 0 {
            let null = ptr::null_mut::<c_void>();
            // SAFETY: plain system calls of the child on itself, with typed
            // variadic arguments for `ptrace`.
            unsafe {
                if libc::ptrace(libc::PTRACE_TRACEME, 0 as libc::pid_t, null, null) == -1 {
                    libc::_exit(1);
                }
                if libc::raise(libc::SIGSTOP) != 0 {
                    libc::_exit(1);
                }
            }
            work();
            // SAFETY: as above.
            unsafe {
                let _ = libc::raise(libc::SIGSTOP);
                libc::_exit(0);
            }
        }
        let count = match wait_child(child) {
            Ok(status) if libc::WIFSTOPPED(status) && libc::WSTOPSIG(status) == libc::SIGSTOP => {
                step_to_stop(child)
            }
            Ok(status) if libc::WIFEXITED(status) => Err(io::Error::other(format!(
                "the traced child exited with status {} before starting",
                libc::WEXITSTATUS(status)
            ))),
            Ok(status) if libc::WIFSTOPPED(status) => Err(io::Error::other(format!(
                "the traced child stopped on signal {} before starting",
                libc::WSTOPSIG(status)
            ))),
            Ok(_) => Err(io::Error::other(
                "the traced child ended before its start was marked",
            )),
            Err(error) => Err(error),
        };
        reap(child);
        count
    }
}
