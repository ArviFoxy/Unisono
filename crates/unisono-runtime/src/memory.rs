// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Keeping the program's memory in place.
//!
//! A page of memory that the system has moved out, or not yet put in, is put
//! in when it is touched, and a real-time thread that touches it waits for
//! the disk or for the system. Locking keeps the pages that the program has
//! in memory. A program therefore locks once everything that its real-time
//! threads use is made and its threads are running.
//!
//! Pages that the program gets later are not locked. Locking them as well
//! would make every later allocation, and every new thread's stack, fail
//! once the system's limit on locked memory is reached, on threads that are
//! not real-time and do allocate.

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
