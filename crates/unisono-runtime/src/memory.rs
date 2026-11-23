// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Process memory locking (`mlockall`) and stack prefaulting for real-time
//! threads.
//!
//! Demand-paged memory can trigger page faults and unbounded disk or kernel
//! stalls on real-time audio threads. Call this module's locking routine once
//! all real-time buffers are allocated and real-time threads have spawned.
//!
//! Only currently resident pages (`MCL_CURRENT`) are locked; `MCL_FUTURE` is
//! intentionally omitted so non-real-time allocations and later thread stacks
//! do not fail if `RLIMIT_MEMLOCK` is tight.

use std::io;

/// Locks the memory that the program has now.
///
/// # Errors
///
/// What the system says: commonly that the program may not lock as much
/// memory, which a limit of the system or a missing privilege decides. The
/// program runs on without it, and a page that is out when it is touched
/// costs that thread a wait.
pub fn lock() -> io::Result<()> {
    #[cfg(target_os = "linux")]
    {
        // SAFETY: `mlockall` takes flags and touches no memory of ours.
        let result = unsafe { libc::mlockall(libc::MCL_CURRENT) };
        if result == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "locking memory is done on Linux only",
        ))
    }
}
