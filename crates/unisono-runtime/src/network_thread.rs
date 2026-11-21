// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A managed background thread for a sender or receiver network loop.
//!
//! [`NetworkThread`] owns the lifecycle of a network thread:
//!
//! - It spawns with a bounded stack ([`STACK_SIZE`]) so `mlockall` does not
//!   pin an 8 MiB default stack.
//! - It applies [`crate::syscalls::restrict`] before entering the loop,
//!   treating `ErrorKind::Unsupported` as non-fatal on platforms without
//!   seccomp filtering and propagating real failures synchronously from
//!   [`NetworkThread::spawn`].
//! - On shutdown it moves the network state (and its UDP socket) back to the
//!   caller through the thread's return value so `close(fd)` and deallocation
//!   always happen outside the seccomp filter.
//! - Its `Drop` implementation signals stop and joins the thread, preventing
//!   leaked sockets or detached background threads on early returns.

use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};

use crate::syscalls;

/// Stack size of a network thread, in bytes (512 KiB).
pub const STACK_SIZE: usize = 512 * 1024;

/// A network loop driven by [`NetworkThread`].
pub trait NetworkLoop: Send + 'static {
    /// Runs one turn of the network loop, waiting at most `milliseconds` for
    /// socket activity.
    ///
    /// # Errors
    ///
    /// A fatal socket error that ends the loop.
    fn turn(&mut self, milliseconds: i32) -> io::Result<()>;
}

/// The state recovered when a [`NetworkThread`] stops.
pub struct Stopped<T> {
    /// The network state returned from the thread, so its socket is dropped
    /// outside the seccomp filter and final counters can be inspected.
    pub network: T,
    /// The fatal error that ended the loop early, if any.
    pub error: Option<io::Error>,
}

struct Shared {
    stop: AtomicBool,
    startup: Mutex<Option<io::Result<bool>>>,
    ready: Condvar,
}

/// A running network thread with RAII shutdown.
pub struct NetworkThread<T: NetworkLoop> {
    // Kept alive until after `handle.join()` completes so the restricted
    // thread never drops the final `Arc` reference or frees `Shared`.
    shared: Arc<Shared>,
    handle: Option<JoinHandle<(T, Option<io::Error>)>>,
    restricted: bool,
}

impl<T: NetworkLoop> NetworkThread<T> {
    /// Spawns a network thread named `name` driving `network` with a poll
    /// timeout of `turn_ms` milliseconds per turn.
    ///
    /// Negative `turn_ms` values are replaced with 20 ms so shutdown always
    /// completes promptly.
    ///
    /// # Errors
    ///
    /// Returns an error if the thread cannot be spawned or if installing the
    /// syscall filter fails on a supported platform.
    pub fn spawn(name: &str, mut network: T, turn_ms: i32) -> io::Result<NetworkThread<T>> {
        let turn_ms = if turn_ms < 0 { 20 } else { turn_ms };
        let shared = Arc::new(Shared {
            stop: AtomicBool::new(false),
            startup: Mutex::new(None),
            ready: Condvar::new(),
        });
        let child_shared = Arc::clone(&shared);
        let handle = thread::Builder::new()
            .name(name.to_owned())
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let restricted = match syscalls::restrict() {
                    Ok(()) => true,
                    Err(error) if error.kind() == io::ErrorKind::Unsupported => false,
                    Err(error) => {
                        let mut guard = child_shared
                            .startup
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner);
                        *guard = Some(Err(error));
                        child_shared.ready.notify_one();
                        drop(guard);
                        return (network, None);
                    }
                };
                {
                    // `Mutex::lock` and `Condvar::notify_one` use only `futex`
                    // (allowed by seccomp) and allocate nothing.
                    let mut guard = child_shared
                        .startup
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    *guard = Some(Ok(restricted));
                    child_shared.ready.notify_one();
                }
                let mut fatal = None;
                while !child_shared.stop.load(Ordering::Acquire) {
                    if let Err(error) = network.turn(turn_ms) {
                        fatal = Some(error);
                        break;
                    }
                }
                // Move `network` (and its `Socket`) out of the restricted
                // thread so `close(fd)` runs on the joining thread instead.
                (network, fatal)
            })?;

        let outcome = {
            let mut guard = shared
                .startup
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            loop {
                if let Some(outcome) = guard.take() {
                    break outcome;
                }
                guard = shared
                    .ready
                    .wait(guard)
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
            }
        };

        match outcome {
            Ok(restricted) => Ok(NetworkThread {
                shared,
                handle: Some(handle),
                restricted,
            }),
            Err(error) => {
                shared.stop.store(true, Ordering::Release);
                let _ = handle.join();
                Err(error)
            }
        }
    }

    /// Whether the thread is running under the syscall restriction filter.
    #[must_use]
    pub fn restricted(&self) -> bool {
        self.restricted
    }

    /// Whether the thread has already stopped (for example after a fatal
    /// socket error).
    #[must_use]
    pub fn is_finished(&self) -> bool {
        self.handle.as_ref().is_none_or(JoinHandle::is_finished)
    }

    /// Asks the thread to stop after its current turn without waiting for it.
    pub fn signal_stop(&self) {
        self.shared.stop.store(true, Ordering::Release);
    }

    /// Signals the thread to stop, waits for it to exit, and returns its
    /// network state and any fatal error.
    ///
    /// # Errors
    ///
    /// Returns an error if the thread panicked.
    pub fn stop(mut self) -> io::Result<Stopped<T>> {
        self.shared.stop.store(true, Ordering::Release);
        let Some(handle) = self.handle.take() else {
            return Err(io::Error::other("network thread was already stopped"));
        };
        let (network, error) = handle
            .join()
            .map_err(|_| io::Error::other("network thread panicked"))?;
        Ok(Stopped { network, error })
    }
}

impl<T: NetworkLoop> Drop for NetworkThread<T> {
    fn drop(&mut self) {
        if let Some(handle) = self.handle.take() {
            self.shared.stop.store(true, Ordering::Release);
            let _ = handle.join();
        }
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use std::io;
    use std::net::{SocketAddr, UdpSocket};
    use std::time::{Duration, Instant};

    use super::{NetworkLoop, NetworkThread};
    use crate::socket::Socket;

    struct EchoLoop {
        socket: Socket,
        buf: [u8; 64],
        turns: u64,
    }

    impl NetworkLoop for EchoLoop {
        fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
            self.socket.wait(milliseconds)?;
            while let Some(received) = self.socket.receive(&mut self.buf)? {
                let bytes = self.buf.get(..received.length).unwrap_or(&[]);
                let _ = self.socket.send_untagged(bytes, received.from);
            }
            self.turns += 1;
            Ok(())
        }
    }

    #[test]
    fn stops_cleanly_under_seccomp_and_releases_port_for_immediate_rebind() {
        let addr: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let socket = Socket::bind(addr).expect("bind");
        let bound = socket.address().expect("local addr");
        let thread = NetworkThread::spawn(
            "test-net",
            EchoLoop {
                socket,
                buf: [0; 64],
                turns: 0,
            },
            5,
        )
        .expect("spawn");
        #[cfg(all(
            target_os = "linux",
            target_endian = "little",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ))]
        assert!(thread.restricted());

        // Exchange a datagram with the restricted thread.
        let client = UdpSocket::bind(addr).expect("client bind");
        client
            .set_read_timeout(Some(Duration::from_secs(2)))
            .expect("timeout");
        client.send_to(b"ping", bound).expect("send");
        let mut reply = [0u8; 16];
        let (len, _) = client.recv_from(&mut reply).expect("recv");
        assert_eq!(&reply[..len], b"ping");

        // Stopping returns the loop state and drops the Socket outside seccomp.
        let stopped = thread.stop().expect("stop");
        assert!(stopped.error.is_none());
        assert!(stopped.network.turns > 0);
        drop(stopped);

        // Immediate rebind to the exact same port proves `close(fd)` succeeded.
        let rebound = UdpSocket::bind(bound).expect("immediate rebind after stop");
        drop(rebound);
    }

    #[test]
    fn drop_stops_thread_and_releases_port() {
        let addr: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let socket = Socket::bind(addr).expect("bind");
        let bound = socket.address().expect("local addr");
        {
            let _thread = NetworkThread::spawn(
                "test-drop",
                EchoLoop {
                    socket,
                    buf: [0; 64],
                    turns: 0,
                },
                5,
            )
            .expect("spawn");
            std::thread::sleep(Duration::from_millis(10));
        }
        let rebound = UdpSocket::bind(bound).expect("immediate rebind after drop");
        drop(rebound);
    }

    #[test]
    fn fatal_turn_error_ends_thread_and_is_reported_by_stop() {
        struct FailAfter(u32);
        impl NetworkLoop for FailAfter {
            fn turn(&mut self, _milliseconds: i32) -> io::Result<()> {
                if self.0 == 0 {
                    return Err(io::Error::from(io::ErrorKind::BrokenPipe));
                }
                self.0 -= 1;
                Ok(())
            }
        }
        let thread = NetworkThread::spawn("test-fail", FailAfter(2), 5).expect("spawn");
        let deadline = Instant::now() + Duration::from_secs(2);
        while !thread.is_finished() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(2));
        }
        assert!(thread.is_finished());
        let stopped = thread.stop().expect("stop");
        assert_eq!(
            stopped.error.map(|e| e.kind()),
            Some(io::ErrorKind::BrokenPipe)
        );
    }
}
