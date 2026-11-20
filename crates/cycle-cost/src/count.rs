// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Counting the instructions that a piece of work executes.
//!
//! The work runs in a child process, and the parent lets the child execute
//! one instruction at a time and counts them. The count is of instructions
//! outside the kernel, and for work that reads no clock and no input it is
//! the same on every run.

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
    use std::io;

    /// Lets the child that waits at a stop run until it stops at the signal
    /// `SIGSTOP` again, one instruction at a time, and returns the number of
    /// instructions it executed.
    fn step_to_stop(child: libc::pid_t) -> io::Result<u64> {
        let mut count = 0u64;
        loop {
            let mut status = 0;
            // SAFETY: `child` is a child of this process that is stopped under
            // its trace, and `status` is a place for one integer.
            let stopped = unsafe {
                if libc::ptrace(libc::PTRACE_SINGLESTEP, child, 0, 0) == -1 {
                    return Err(io::Error::last_os_error());
                }
                libc::waitpid(child, &raw mut status, 0)
            };
            if stopped == -1 {
                return Err(io::Error::last_os_error());
            }
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
            // SAFETY: plain system calls of the child on itself.
            unsafe {
                libc::ptrace(libc::PTRACE_TRACEME, 0, 0, 0);
                libc::raise(libc::SIGSTOP);
            }
            work();
            // SAFETY: as above.
            unsafe {
                libc::raise(libc::SIGSTOP);
                libc::_exit(0);
            }
        }
        let mut status = 0;
        // SAFETY: `child` is a child of this process, and `status` is a place
        // for one integer.
        if unsafe { libc::waitpid(child, &raw mut status, 0) } == -1 {
            return Err(io::Error::last_os_error());
        }
        let count = step_to_stop(child);
        // SAFETY: `child` is a child of this process; it is ended and collected
        // whatever state it is in.
        unsafe {
            libc::kill(child, libc::SIGKILL);
            libc::waitpid(child, &raw mut status, 0);
        }
        count
    }
}
