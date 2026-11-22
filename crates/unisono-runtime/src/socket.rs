// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Datagrams with the times at which they arrived and left.
//!
//! A [`Socket`] is a UDP socket that does not block. With every datagram it
//! receives it gives the time of arrival, and for every datagram it sent it
//! reports, a little later, the time of departure, together with the tag the
//! caller gave the datagram. All times are readings of the raw clock of
//! [`crate::clock`].
//!
//! # Where a time comes from
//!
//! Each [`Stamp`] says which of three sources it has.
//!
//! - **The kernel** stamped the datagram on its way in, or when it handed it
//!   to the network device on its way out. These are the stamps to want: a
//!   program is woken some time after a datagram arrived, and that time grows
//!   to milliseconds on a busy host, while the kernel's stamp does not move.
//! - **The packet scheduler**: the kernel stamped an outgoing datagram when
//!   it entered the queue before the device. Every device gives this; it is
//!   earlier than the departure by the time spent in the queue.
//! - **The program** read the clock itself. A departure is then stamped
//!   before the datagram is sent and an arrival after it was received, so
//!   that the error always makes the datagram look slower, never faster: an
//!   estimate built on the fastest datagrams is then merely worse, not wrong.
//!
//! The kernel stamps with the system clock. A [`crate::clock::Tracker`] turns
//! that into the raw clock, and the stamp carries the error of that
//! conversion. A kernel stamp that is further than [`LONGEST_AGE`] from the
//! tracker's latest measurement is not converted, and the program's own
//! stamp takes its place.
//!
//! Kernel stamps exist on Linux. On another system every stamp is the
//! program's, and the socket says so.
//!
//! # Use
//!
//! One thread owns the socket. It calls [`Socket::wait`], then
//! [`Socket::receive`] and [`Socket::departure`] until each has nothing
//! more. Nothing in sending, receiving or reporting allocates memory.

use std::io;
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, UdpSocket};

use crate::clock::{self, System, SystemNs, Tracker};

/// How far a kernel stamp may be from the latest measurement of the clocks
/// and still be converted, in nanoseconds: 50 ms.
pub const LONGEST_AGE: i64 = 50_000_000;

/// After how long the clocks are measured again before a conversion, in
/// nanoseconds.
const REFRESH: i64 = 100_000;

/// How many sent datagrams can wait for their departure at once, and how many
/// departures can wait to be read. A caller that sends more than this many
/// datagrams without reading departures loses the oldest ones.
pub const WAITING: usize = 64;

/// Maximum kernel error-queue reports inspected during a single
/// [`Socket::departure`] call, large enough to drain every [`WAITING`]
/// scheduled/delivered pair plus bursts of unrelated error-queue messages.
const MAX_REPORTS_PER_CALL: usize = WAITING * 8;

/// Canonicalizes a peer address for equality comparisons: IPv4-mapped IPv6
/// addresses (`::ffff:a.b.c.d`) are folded to their IPv4 form so dual-stack
/// sockets match IPv4 peer entries.
#[must_use]
pub fn canonical_addr(address: SocketAddr) -> SocketAddr {
    match address {
        SocketAddr::V4(_) => address,
        SocketAddr::V6(v6) => match v6.ip().to_ipv4_mapped() {
            Some(v4) => SocketAddr::V4(SocketAddrV4::new(v4, v6.port())),
            None => address,
        },
    }
}

/// Returns an ephemeral unspecified bind address matching the address family
/// of `peers` (`[::]:0` if any peer is IPv6, otherwise `0.0.0.0:0`).
#[must_use]
pub fn unspecified_for(peers: &[SocketAddr]) -> SocketAddr {
    if peers.iter().any(SocketAddr::is_ipv6) {
        SocketAddr::from((Ipv6Addr::UNSPECIFIED, 0))
    } else {
        SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0))
    }
}

/// Whether a UDP `send_to` error is transient or per-destination and should be
/// counted instead of terminating the network thread.
///
/// `EACCES` (for example sending to a broadcast address without `SO_BROADCAST`)
/// is treated as fatal so misconfiguration surfaces immediately. `EPERM` (for
/// example a firewall rule dropping packets to one receiver) and
/// `EADDRNOTAVAIL` (for example a temporary address change) stay transient and
/// per-destination so one peer cannot stop delivery to other receivers; use
/// [`is_restricted_send_error`] to count them separately.
#[must_use]
pub fn is_transient_send_error(error: &io::Error) -> bool {
    #[cfg(unix)]
    if let Some(code) = error.raw_os_error() {
        if code == libc::EACCES {
            return false;
        }
        if matches!(code, libc::ENOBUFS | libc::EPERM | libc::EADDRNOTAVAIL) {
            return true;
        }
    }
    matches!(
        error.kind(),
        io::ErrorKind::WouldBlock
            | io::ErrorKind::Interrupted
            | io::ErrorKind::NetworkUnreachable
            | io::ErrorKind::HostUnreachable
            | io::ErrorKind::NetworkDown
            | io::ErrorKind::ConnectionRefused
            | io::ErrorKind::ConnectionReset
            | io::ErrorKind::AddrNotAvailable
    )
}

/// Whether a transient UDP `send_to` error was caused by a per-destination
/// policy or address-availability failure (`EPERM` or `EADDRNOTAVAIL` on Unix;
/// `AddrNotAvailable` elsewhere), which is counted separately from generic
/// transient errors so firewall drops and address changes stay visible.
#[must_use]
pub fn is_restricted_send_error(error: &io::Error) -> bool {
    #[cfg(unix)]
    if let Some(code) = error.raw_os_error() {
        return matches!(code, libc::EPERM | libc::EADDRNOTAVAIL);
    }
    error.kind() == io::ErrorKind::AddrNotAvailable
}

/// After how many datagrams with a stamp of the packet scheduler and none of
/// the device the socket concludes that the device gives none. Large enough
/// not to trip on brief transmit-queue bursts while still settling well within
/// [`WAITING`].
const PATIENCE: u32 = 16;

/// With how many datagrams sent and no report waiting for any of them the
/// socket concludes that the kernel gives none.
const SILENCE: usize = 32;

/// Where a stamp comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    /// The kernel, at arrival or at the hand-over to the network device.
    Kernel,
    /// The kernel, when the datagram entered the queue before the device.
    Scheduler,
    /// The program, before sending or after receiving.
    Program,
}

/// A time at which a datagram arrived or left.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stamp {
    /// The reading of the raw clock, in nanoseconds.
    pub time: i64,
    /// How far the conversion from the kernel's clock may be off either way,
    /// in nanoseconds; zero for a stamp of the program, which is late by an
    /// amount nobody knows instead.
    pub error: i64,
    /// Where the time comes from.
    pub source: Source,
}

/// A datagram that was received.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Received {
    /// The number of bytes written to the buffer.
    pub length: usize,
    /// Who sent it.
    pub from: SocketAddr,
    /// When it arrived.
    pub arrival: Stamp,
    /// The raw clock when the program had received it.
    pub read: i64,
}

/// What sending a datagram returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sent {
    /// The raw clock just before the datagram was sent.
    pub before: i64,
}

/// The departure of a datagram that was sent earlier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Departure {
    /// The tag the caller gave the datagram.
    pub tag: u64,
    /// When it left.
    pub stamp: Stamp,
}

/// What a socket has waiting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ready {
    /// A datagram can be received.
    pub datagrams: bool,
    /// A departure may be reported.
    pub departures: bool,
}

/// A datagram that was sent and whose departure the kernel has yet to
/// report.
#[derive(Clone, Copy)]
struct Awaited {
    /// Tag to hand back with the departure, or `None` for untagged sends
    /// whose kernel key must still be tracked without reporting a departure.
    tag: Option<u64>,
    before: i64,
    /// The key the kernel gives the datagram in its reports, if no send that
    /// failed since the last report took a key.
    key: u32,
    /// By how much the kernel's key may be larger: the number of sends that
    /// failed before this datagram and may each have taken a key.
    slack: u32,
    /// The kernel's stamp of the entry into the queue, on the system clock.
    scheduled: Option<i64>,
    /// Whether the departure is still to be reported.
    open: bool,
}

const NOTHING: Awaited = Awaited {
    tag: None,
    before: 0,
    key: 0,
    slack: 0,
    scheduled: None,
    open: false,
};

/// What is known of the departure of a datagram.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Known {
    tag: u64,
    /// The raw clock just before the datagram was sent.
    before: i64,
    /// The kernel's stamp, on the system clock, and what it is of. Without
    /// it the program's stamp is all there is.
    kernel: Option<(i64, Source)>,
}

/// Which datagram each of the kernel's reports belongs to.
///
/// The kernel numbers the datagrams of a socket and reports, for each
/// number, when the datagram entered the queue before the device and when
/// it was handed to the device. The ledger keeps the datagrams that were
/// sent, in order, and gives each report to its datagram.
///
/// Three things can go wrong and are dealt with here. A send that fails may
/// or may not have used up a number, depending on where in the kernel it
/// failed: the reports of entry into the queue come in the order of the
/// sends, so the first one after such a send shows which it was. A device
/// may not stamp what it is handed: after a few datagrams with one report
/// and not the other, the stamps of the queue are handed out. A kernel may
/// report nothing at all: when its queue of reports is empty though many
/// datagrams were sent, the program's stamps are handed out.
struct Ledger {
    /// Whether the kernel was asked for reports.
    reports: bool,
    /// Which stamps departures get, once that is known.
    decided: Option<Source>,
    /// The datagrams that wait for their departure, oldest first, in a ring.
    awaited: [Awaited; WAITING],
    oldest: usize,
    waiting: usize,
    /// The key the kernel gives the next datagram, if no failed send took
    /// one.
    next_key: u32,
    /// Sends that failed since the last report settled the keys.
    failed: u32,
    /// Datagrams with a stamp of the queue that got none of the device since
    /// the device last gave one.
    undelivered: u32,
    /// Departures that are ready to be handed out, oldest first, in a ring.
    ready: [Option<Known>; WAITING],
    first_ready: usize,
    readies: usize,
}

fn place(index: usize) -> usize {
    index % WAITING
}

impl Ledger {
    fn new(reports: bool) -> Ledger {
        Ledger {
            reports,
            decided: if reports { None } else { Some(Source::Program) },
            awaited: [NOTHING; WAITING],
            oldest: 0,
            waiting: 0,
            next_key: 0,
            failed: 0,
            undelivered: 0,
            ready: [None; WAITING],
            first_ready: 0,
            readies: 0,
        }
    }

    /// Queues a departure to be handed out; the oldest gives way when there
    /// is no room.
    fn hand_out(&mut self, known: Known) {
        if self.readies == WAITING {
            self.first_ready = place(self.first_ready + 1);
            self.readies -= 1;
        }
        let at = place(self.first_ready + self.readies);
        if let Some(slot) = self.ready.get_mut(at) {
            *slot = Some(known);
            self.readies += 1;
        }
    }

    /// The next departure that is ready, if any.
    fn next(&mut self) -> Option<Known> {
        while self.readies > 0 {
            let known = self.ready.get_mut(self.first_ready).and_then(Option::take);
            self.first_ready = place(self.first_ready + 1);
            self.readies -= 1;
            if known.is_some() {
                return known;
            }
        }
        None
    }

    /// Takes in that a send failed. The kernel may or may not have counted
    /// the datagram.
    fn failed(&mut self) {
        self.failed = self.failed.saturating_add(1);
    }

    /// Takes in that a datagram was sent, with an optional `tag` to report
    /// when its departure is known.
    fn sent(&mut self, tag: Option<u64>, before: i64) {
        if self.decided == Some(Source::Program) {
            // The kernel counts the datagram whether or not it reports.
            self.next_key = self.next_key.wrapping_add(1);
            if let Some(tag) = tag {
                self.hand_out(Known {
                    tag,
                    before,
                    kernel: None,
                });
            }
            return;
        }
        if self.waiting == WAITING {
            self.oldest = place(self.oldest + 1);
            self.waiting -= 1;
        }
        let at = place(self.oldest + self.waiting);
        if let Some(slot) = self.awaited.get_mut(at) {
            *slot = Awaited {
                tag,
                before,
                key: self.next_key,
                slack: self.failed,
                scheduled: None,
                open: true,
            };
            self.waiting += 1;
        }
        self.next_key = self.next_key.wrapping_add(1);
    }

    /// Takes in that the kernel's queue of reports was found empty. The
    /// report that a datagram entered the queue before the device is made
    /// while the datagram is sent, so many datagrams without one mean that
    /// the kernel took the request for reports and makes none.
    fn quiet(&mut self) {
        if self.decided.is_some() {
            return;
        }
        let unreported = (0..self.waiting)
            .filter_map(|step| self.awaited.get(place(self.oldest + step)))
            .filter(|awaited| awaited.open && awaited.scheduled.is_none())
            .count();
        if unreported <= SILENCE {
            return;
        }
        // Hand out the program's stamps for everything tagged that waits, and
        // from now on.
        self.decided = Some(Source::Program);
        for step in 0..self.waiting {
            let at = place(self.oldest + step);
            if let Some(awaited) = self.awaited.get(at).copied().filter(|awaited| awaited.open)
                && let Some(tag) = awaited.tag
            {
                self.hand_out(Known {
                    tag,
                    before: awaited.before,
                    kernel: None,
                });
            }
        }
        self.waiting = 0;
    }

    /// Forgets the datagrams at the old end that wait for nothing more.
    fn forget_closed(&mut self) {
        while self.waiting > 0 {
            let open = self
                .awaited
                .get(self.oldest)
                .is_some_and(|awaited| awaited.open);
            if open {
                break;
            }
            self.oldest = place(self.oldest + 1);
            self.waiting -= 1;
        }
    }

    /// Takes in the kernel's report that the datagram with `key` entered the
    /// queue before the device at `system`.
    ///
    /// These reports come in the order of the sends, so the report belongs
    /// to the oldest datagram that has none yet and whose key it can be. A
    /// datagram before that one never reached the queue.
    fn scheduled(&mut self, key: u32, system: i64) {
        for step in 0..self.waiting {
            let at = place(self.oldest + step);
            let Some(awaited) = self.awaited.get(at).copied() else {
                break;
            };
            if !awaited.open || awaited.scheduled.is_some() {
                continue;
            }
            let beyond = key.wrapping_sub(awaited.key);
            if beyond > u32::MAX / 2 {
                // A report of a datagram that is no longer kept.
                break;
            }
            if beyond > awaited.slack {
                // This datagram got no report: it did not reach the queue.
                if let Some(slot) = self.awaited.get_mut(at) {
                    slot.open = false;
                }
                continue;
            }
            // Of the sends that failed before this datagram, `beyond` took a
            // key. That settles the key of this datagram and shifts those of
            // all later ones.
            for later in step..self.waiting {
                if let Some(slot) = self.awaited.get_mut(place(self.oldest + later)) {
                    slot.key = slot.key.wrapping_add(beyond);
                    slot.slack = slot.slack.saturating_sub(awaited.slack);
                }
            }
            self.next_key = self.next_key.wrapping_add(beyond);
            self.failed = self.failed.saturating_sub(awaited.slack);
            if let Some(slot) = self.awaited.get_mut(at) {
                slot.scheduled = Some(system);
            }
            if self.decided == Some(Source::Scheduler) {
                self.close(at, system, Source::Scheduler);
            } else if self.decided.is_none() {
                self.undelivered += 1;
                if self.undelivered > PATIENCE {
                    self.settle_for_scheduler();
                }
            }
            break;
        }
        self.forget_closed();
    }

    /// Takes in the kernel's report that the datagram with `key` was handed
    /// to the device at `system`.
    fn delivered(&mut self, key: u32, system: i64) {
        self.decided = Some(Source::Kernel);
        self.undelivered = 0;
        for step in 0..self.waiting {
            let at = place(self.oldest + step);
            let found = self.awaited.get(at).is_some_and(|awaited| {
                awaited.open && awaited.scheduled.is_some() && awaited.key == key
            });
            if found {
                self.close(at, system, Source::Kernel);
                break;
            }
        }
        self.forget_closed();
    }

    /// Hands out the departure of the awaited datagram at place `at`, if it
    /// carried a tag.
    fn close(&mut self, at: usize, system: i64, source: Source) {
        let Some(awaited) = self.awaited.get(at).copied() else {
            return;
        };
        if let Some(slot) = self.awaited.get_mut(at) {
            slot.open = false;
        }
        if let Some(tag) = awaited.tag {
            self.hand_out(Known {
                tag,
                before: awaited.before,
                kernel: Some((system, source)),
            });
        }
    }

    /// Concludes that the device stamps nothing, and hands out the stamps of
    /// the queue for everything that has one, and from now on.
    fn settle_for_scheduler(&mut self) {
        self.decided = Some(Source::Scheduler);
        for step in 0..self.waiting {
            let at = place(self.oldest + step);
            let scheduled = self
                .awaited
                .get(at)
                .filter(|awaited| awaited.open)
                .and_then(|awaited| awaited.scheduled);
            if let Some(system) = scheduled {
                self.close(at, system, Source::Scheduler);
            }
        }
    }
}

/// A UDP socket that gives the times of arrival and departure.
pub struct Socket {
    inner: UdpSocket,
    tracker: Tracker<System>,
    /// Whether the kernel stamps arrivals on this socket.
    arrivals: bool,
    ledger: Ledger,
}

impl Socket {
    /// A socket bound to `address`.
    ///
    /// # Errors
    ///
    /// What the system says when it cannot make the socket, and
    /// `Unsupported` when the host lacks the clocks.
    pub fn bind(address: SocketAddr) -> io::Result<Socket> {
        if !clock::supported() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "this host has no raw monotonic clock",
            ));
        }
        let socket = UdpSocket::bind(address)?;
        socket.set_nonblocking(true)?;
        let (arrivals, reports) = sys::enable(&socket);
        let mut tracker = Tracker::system(LONGEST_AGE);
        tracker.refresh();
        Ok(Socket {
            inner: socket,
            tracker,
            arrivals,
            ledger: Ledger::new(reports),
        })
    }

    /// The address the socket is bound to.
    ///
    /// # Errors
    ///
    /// What the system says.
    pub fn address(&self) -> io::Result<SocketAddr> {
        self.inner.local_addr()
    }

    /// The socket itself, for options that this type does not set.
    #[must_use]
    pub fn inner(&self) -> &UdpSocket {
        &self.inner
    }

    /// Where the stamps of arrivals come from.
    #[must_use]
    pub fn arrivals(&self) -> Source {
        if self.arrivals {
            Source::Kernel
        } else {
            Source::Program
        }
    }

    /// Where the stamps of departures come from, once the socket has sent
    /// enough to know.
    #[must_use]
    pub fn departures(&self) -> Option<Source> {
        self.ledger.decided
    }

    /// Waits until a datagram or a report of a departure is there, for at
    /// most `milliseconds`; a negative number waits without limit.
    ///
    /// # Errors
    ///
    /// What the system says.
    pub fn wait(&self, milliseconds: i32) -> io::Result<Ready> {
        if self.ledger.readies > 0 {
            return Ok(Ready {
                datagrams: false,
                departures: true,
            });
        }
        sys::wait(&self.inner, milliseconds)
    }

    /// The program's own stamp.
    fn own(time: i64) -> Stamp {
        Stamp {
            time,
            error: 0,
            source: Source::Program,
        }
    }

    /// A stamp of the kernel on the raw clock, or the program's stamp if
    /// the kernel's cannot be converted.
    fn converted(&mut self, system: i64, source: Source, own: i64) -> Stamp {
        self.tracker.refresh_if_older(clock::raw_ns(), REFRESH);
        match self.tracker.to_raw(SystemNs(system)) {
            Ok(converted) => Stamp {
                time: converted.time.as_i64(),
                error: converted.error,
                source,
            },
            Err(_) => Socket::own(own),
        }
    }

    /// Receives a datagram into `buffer`, if one is there. A datagram longer
    /// than the buffer is cut.
    ///
    /// # Errors
    ///
    /// What the system says.
    pub fn receive(&mut self, buffer: &mut [u8]) -> io::Result<Option<Received>> {
        let Some(datagram) = sys::receive(&self.inner, buffer)? else {
            return Ok(None);
        };
        let read = clock::raw();
        let arrival = match datagram.stamped {
            Some(system) if self.arrivals => self.converted(system, Source::Kernel, read),
            _ => Socket::own(read),
        };
        Ok(Some(Received {
            length: datagram.length,
            from: datagram.from,
            arrival,
            read,
        }))
    }

    /// Sends `bytes` to `to`, optionally tracking `tag` for a departure
    /// report while always keeping kernel timestamp keys synchronized.
    fn send_raw(&mut self, bytes: &[u8], to: SocketAddr, tag: Option<u64>) -> io::Result<Sent> {
        let before = clock::raw();
        if let Err(error) = self.inner.send_to(bytes, to) {
            self.ledger.failed();
            return Err(error);
        }
        self.ledger.sent(tag, before);
        Ok(Sent { before })
    }

    /// Sends `bytes` to `to`. `tag` comes back with the departure.
    ///
    /// # Errors
    ///
    /// What the system says; `WouldBlock` when the socket's buffer is full.
    pub fn send_to(&mut self, bytes: &[u8], to: SocketAddr, tag: u64) -> io::Result<Sent> {
        self.send_raw(bytes, to, Some(tag))
    }

    /// Sends `bytes` to `to` without reporting a departure, while still
    /// keeping the kernel's per-datagram timestamp sequence aligned.
    ///
    /// # Errors
    ///
    /// What the system says; `WouldBlock` when the socket's buffer is full.
    pub fn send_untagged(&mut self, bytes: &[u8], to: SocketAddr) -> io::Result<Sent> {
        self.send_raw(bytes, to, None)
    }

    /// The departure of a datagram that was sent earlier, if one is known
    /// now. Departures come in the order in which the kernel reports them,
    /// which is the order of the sends unless the device reorders. At most
    /// [`WAITING`] of them wait to be read.
    ///
    /// # Errors
    ///
    /// What the system says.
    pub fn departure(&mut self) -> io::Result<Option<Departure>> {
        // Each round takes one report from the kernel; the budget covers all
        // `WAITING` scheduled/delivered pairs plus bursts of non-timestamp
        // error-queue messages.
        for _ in 0..MAX_REPORTS_PER_CALL {
            if let Some(known) = self.ledger.next() {
                let stamp = match known.kernel {
                    Some((system, source)) => self.converted(system, source, known.before),
                    None => Socket::own(known.before),
                };
                return Ok(Some(Departure {
                    tag: known.tag,
                    stamp,
                }));
            }
            if !self.ledger.reports {
                break;
            }
            match sys::report(&self.inner)? {
                sys::Reported::Nothing => {
                    self.ledger.quiet();
                    if self.ledger.readies == 0 {
                        break;
                    }
                }
                sys::Reported::Other => {}
                sys::Reported::Scheduled { key, system } => self.ledger.scheduled(key, system),
                sys::Reported::Delivered { key, system } => self.ledger.delivered(key, system),
            }
        }
        Ok(None)
    }
}

#[cfg(unix)]
impl std::os::fd::AsRawFd for Socket {
    fn as_raw_fd(&self) -> std::os::fd::RawFd {
        self.inner.as_raw_fd()
    }
}

/// What the system calls give, on Linux.
#[cfg(target_os = "linux")]
mod sys {
    use std::io;
    use std::mem::{size_of, zeroed};
    use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, UdpSocket};
    use std::os::fd::AsRawFd;
    use std::ptr;

    use super::Ready;

    /// The kernel's name for a report that a datagram was handed to the
    /// device (`SCM_TSTAMP_SND` in `linux/errqueue.h`).
    const HANDED_TO_DEVICE: u32 = 0;

    /// The kernel's name for a report that a datagram entered the queue
    /// before the device (`SCM_TSTAMP_SCHED`).
    const ENTERED_QUEUE: u32 = 1;

    /// A datagram as the kernel gave it.
    pub(super) struct Datagram {
        pub(super) length: usize,
        pub(super) from: SocketAddr,
        /// The kernel's stamp of the arrival, on the system clock.
        pub(super) stamped: Option<i64>,
    }

    /// What the socket's queue of reports held.
    pub(super) enum Reported {
        /// Nothing.
        Nothing,
        /// Something that is no report of a departure.
        Other,
        /// The datagram with `key` entered the queue before the device.
        Scheduled { key: u32, system: i64 },
        /// The datagram with `key` was handed to the device.
        Delivered { key: u32, system: i64 },
    }

    /// The size of a small type as the system calls want it.
    fn length_of<T>() -> libc::socklen_t {
        // The types here are a few bytes to a few hundred.
        #[allow(clippy::cast_possible_truncation)]
        let length = size_of::<T>() as libc::socklen_t;
        length
    }

    fn set(socket: &UdpSocket, flags: u32) -> bool {
        // SAFETY: the option takes an `int`-sized set of flags, which `flags`
        // is, and the pointer and the size describe it for the length of the
        // call.
        let result = unsafe {
            libc::setsockopt(
                socket.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_TIMESTAMPING,
                ptr::from_ref(&flags).cast(),
                length_of::<u32>(),
            )
        };
        result == 0
    }

    /// Asks the kernel for stamps, and says whether it stamps arrivals and
    /// whether it reports departures.
    pub(super) fn enable(socket: &UdpSocket) -> (bool, bool) {
        let arrivals = libc::SOF_TIMESTAMPING_RX_SOFTWARE | libc::SOF_TIMESTAMPING_SOFTWARE;
        // Reports carry the number of the datagram and no copy of it.
        let departures = libc::SOF_TIMESTAMPING_TX_SOFTWARE
            | libc::SOF_TIMESTAMPING_TX_SCHED
            | libc::SOF_TIMESTAMPING_OPT_ID
            | libc::SOF_TIMESTAMPING_OPT_TSONLY;
        if set(socket, arrivals | departures) {
            (true, true)
        } else {
            (set(socket, arrivals), false)
        }
    }

    pub(super) fn wait(socket: &UdpSocket, milliseconds: i32) -> io::Result<Ready> {
        let mut poll = libc::pollfd {
            fd: socket.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        // SAFETY: `poll` is one valid `pollfd`, and the count says one.
        let result = unsafe { libc::poll(&raw mut poll, 1, milliseconds) };
        if result < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                return Ok(Ready {
                    datagrams: false,
                    departures: false,
                });
            }
            return Err(error);
        }
        Ok(Ready {
            datagrams: poll.revents & libc::POLLIN != 0,
            // The kernel signals its queue of reports as an error condition.
            departures: poll.revents & libc::POLLERR != 0,
        })
    }

    /// Room for the control messages of one datagram, aligned for their
    /// headers.
    #[repr(align(8))]
    struct Control([u8; 256]);

    /// A stamp as nanoseconds of the system clock.
    fn nanos(time: &libc::timespec) -> i64 {
        // The fields are 32 bits wide on some targets and 64 on others.
        #[allow(clippy::useless_conversion)]
        let (seconds, nanos) = (i64::from(time.tv_sec), i64::from(time.tv_nsec));
        seconds.saturating_mul(1_000_000_000).saturating_add(nanos)
    }

    /// The address in `storage`, which the kernel filled to `length` bytes.
    fn address(storage: &libc::sockaddr_storage, length: usize) -> Option<SocketAddr> {
        match libc::c_int::from(storage.ss_family) {
            libc::AF_INET if length >= size_of::<libc::sockaddr_in>() => {
                // SAFETY: the family says the storage holds a `sockaddr_in`,
                // the kernel filled at least that many bytes, and the storage
                // is aligned for every socket address type.
                let v4 = unsafe { &*ptr::from_ref(storage).cast::<libc::sockaddr_in>() };
                Some(SocketAddr::V4(SocketAddrV4::new(
                    Ipv4Addr::from(u32::from_be(v4.sin_addr.s_addr)),
                    u16::from_be(v4.sin_port),
                )))
            }
            libc::AF_INET6 if length >= size_of::<libc::sockaddr_in6>() => {
                // SAFETY: as above, for a `sockaddr_in6`.
                let v6 = unsafe { &*ptr::from_ref(storage).cast::<libc::sockaddr_in6>() };
                Some(SocketAddr::V6(SocketAddrV6::new(
                    Ipv6Addr::from(v6.sin6_addr.s6_addr),
                    u16::from_be(v6.sin6_port),
                    v6.sin6_flowinfo,
                    v6.sin6_scope_id,
                )))
            }
            _ => None,
        }
    }

    /// What one `recvmsg` gave.
    struct Message {
        length: usize,
        from: Option<SocketAddr>,
        /// The kernel's software stamp among the control messages.
        stamped: Option<i64>,
        /// The kind and key of a report of a departure among them.
        report: Option<(u32, u32)>,
    }

    /// Receives one message with its control messages, from the socket or,
    /// with `MSG_ERRQUEUE` in `flags`, from its queue of reports. `None`
    /// when there is nothing.
    fn message(
        socket: &UdpSocket,
        buffer: &mut [u8],
        flags: libc::c_int,
    ) -> io::Result<Option<Message>> {
        let mut vector = libc::iovec {
            iov_base: buffer.as_mut_ptr().cast(),
            iov_len: buffer.len(),
        };
        let mut control = Control([0; 256]);
        // SAFETY: all-zero bytes are a valid `sockaddr_storage`.
        let mut name: libc::sockaddr_storage = unsafe { zeroed() };
        // SAFETY: all-zero bytes are a valid `msghdr`: null pointers and
        // zero lengths. Some targets give it padding that cannot be named.
        let mut header: libc::msghdr = unsafe { zeroed() };
        header.msg_name = ptr::from_mut(&mut name).cast();
        header.msg_namelen = length_of::<libc::sockaddr_storage>();
        header.msg_iov = &raw mut vector;
        header.msg_iovlen = 1;
        header.msg_control = control.0.as_mut_ptr().cast();
        // 256, in the integer type that the target gives this field.
        #[allow(clippy::cast_possible_truncation)]
        let room = control.0.len() as _;
        header.msg_controllen = room;
        // SAFETY: the header points at a name, one buffer and a control
        // area that all live through the call, with their true lengths.
        let length = unsafe {
            libc::recvmsg(
                socket.as_raw_fd(),
                &raw mut header,
                flags | libc::MSG_DONTWAIT,
            )
        };
        if length < 0 {
            let error = io::Error::last_os_error();
            return match error.kind() {
                io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted => Ok(None),
                _ => Err(error),
            };
        }
        let mut found = Message {
            length: usize::try_from(length).unwrap_or(0),
            from: address(&name, header.msg_namelen as usize),
            stamped: None,
            report: None,
        };
        #[allow(clippy::unnecessary_cast)]
        let control_len = (header.msg_controllen as usize).min(control.0.len());
        let control_start = control.0.as_ptr() as usize;
        let control_end = control_start.saturating_add(control_len);
        // SAFETY: the header is the one `recvmsg` filled, so its control
        // area holds whole control messages up to `msg_controllen`.
        let mut control_message = unsafe { libc::CMSG_FIRSTHDR(&raw const header) };
        while !control_message.is_null() {
            // SAFETY: the pointer is not null and comes from the kernel's
            // chain of control messages in an area aligned for them.
            #[allow(clippy::unnecessary_cast)]
            let (level, kind, cmsg_len) = unsafe {
                (
                    (*control_message).cmsg_level,
                    (*control_message).cmsg_type,
                    (*control_message).cmsg_len as usize,
                )
            };
            // SAFETY: the data of a control message follows its header
            // inside the control area.
            let data = unsafe { libc::CMSG_DATA(control_message) };
            let data_addr = data as usize;
            let available = control_end.saturating_sub(data_addr);
            if level == libc::SOL_SOCKET && kind == libc::SCM_TIMESTAMPING {
                // SAFETY: `CMSG_LEN` is a pure size calculation on a small struct.
                let needed = unsafe { libc::CMSG_LEN(length_of::<libc::timespec>()) } as usize;
                if cmsg_len >= needed && available >= size_of::<libc::timespec>() {
                    // SAFETY: `cmsg_len` and `control_end` both confirm that a
                    // full `timespec` (the first of the three in
                    // `SCM_TIMESTAMPING`) lies inside the control buffer; it
                    // need not be aligned, so it is read unaligned.
                    let software = unsafe { ptr::read_unaligned(data.cast::<libc::timespec>()) };
                    found.stamped = Some(nanos(&software));
                }
            } else if (level == libc::SOL_IP && kind == libc::IP_RECVERR)
                || (level == libc::SOL_IPV6 && kind == libc::IPV6_RECVERR)
            {
                // SAFETY: `CMSG_LEN` is a pure size calculation on a small struct.
                let needed =
                    unsafe { libc::CMSG_LEN(length_of::<libc::sock_extended_err>()) } as usize;
                if cmsg_len >= needed && available >= size_of::<libc::sock_extended_err>() {
                    // SAFETY: `cmsg_len` and `control_end` both confirm that a
                    // full `sock_extended_err` lies inside the control buffer;
                    // read unaligned as above.
                    let report =
                        unsafe { ptr::read_unaligned(data.cast::<libc::sock_extended_err>()) };
                    let is_stamp = report.ee_errno == libc::ENOMSG as u32
                        && report.ee_origin == libc::SO_EE_ORIGIN_TIMESTAMPING;
                    if is_stamp {
                        found.report = Some((report.ee_info, report.ee_data));
                    }
                }
            }
            // SAFETY: both pointers are the ones this loop got from the
            // kernel's chain.
            control_message = unsafe { libc::CMSG_NXTHDR(&raw const header, control_message) };
        }
        Ok(Some(found))
    }

    pub(super) fn receive(socket: &UdpSocket, buffer: &mut [u8]) -> io::Result<Option<Datagram>> {
        let Some(found) = message(socket, buffer, 0)? else {
            return Ok(None);
        };
        let Some(from) = found.from else {
            return Err(io::Error::from(io::ErrorKind::InvalidData));
        };
        Ok(Some(Datagram {
            length: found.length,
            from,
            stamped: found.stamped,
        }))
    }

    pub(super) fn report(socket: &UdpSocket) -> io::Result<Reported> {
        let Some(found) = message(socket, &mut [], libc::MSG_ERRQUEUE)? else {
            return Ok(Reported::Nothing);
        };
        Ok(match (found.report, found.stamped) {
            (Some((ENTERED_QUEUE, key)), Some(system)) => Reported::Scheduled { key, system },
            (Some((HANDED_TO_DEVICE, key)), Some(system)) => Reported::Delivered { key, system },
            _ => Reported::Other,
        })
    }
}

/// What the system calls give where the kernel stamps nothing.
#[cfg(not(target_os = "linux"))]
mod sys {
    use std::io;
    use std::net::{SocketAddr, UdpSocket};

    use super::Ready;

    pub(super) struct Datagram {
        pub(super) length: usize,
        pub(super) from: SocketAddr,
        pub(super) stamped: Option<i64>,
    }

    pub(super) enum Reported {
        Nothing,
        #[allow(dead_code)] // only a kernel that reports gives these
        Other,
        #[allow(dead_code)]
        Scheduled {
            key: u32,
            system: i64,
        },
        #[allow(dead_code)]
        Delivered {
            key: u32,
            system: i64,
        },
    }

    pub(super) fn enable(_socket: &UdpSocket) -> (bool, bool) {
        (false, false)
    }

    #[cfg(unix)]
    pub(super) fn wait(socket: &UdpSocket, milliseconds: i32) -> io::Result<Ready> {
        use std::os::fd::AsRawFd;
        let mut poll = libc::pollfd {
            fd: socket.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        // SAFETY: `poll` is one valid `pollfd`, and the count says one.
        let result = unsafe { libc::poll(&raw mut poll, 1, milliseconds) };
        if result < 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
        Ok(Ready {
            datagrams: poll.revents & libc::POLLIN != 0,
            departures: false,
        })
    }

    #[cfg(not(unix))]
    pub(super) fn wait(_socket: &UdpSocket, _milliseconds: i32) -> io::Result<Ready> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "waiting for a socket is not built for this system",
        ))
    }

    pub(super) fn receive(socket: &UdpSocket, buffer: &mut [u8]) -> io::Result<Option<Datagram>> {
        match socket.recv_from(buffer) {
            Ok((length, from)) => Ok(Some(Datagram {
                length,
                from,
                stamped: None,
            })),
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                ) =>
            {
                Ok(None)
            }
            Err(error) => Err(error),
        }
    }

    #[allow(clippy::unnecessary_wraps)] // the signature of the version that asks the kernel
    pub(super) fn report(_socket: &UdpSocket) -> io::Result<Reported> {
        Ok(Reported::Nothing)
    }
}

#[cfg(test)]
mod tests {
    use std::net::SocketAddr;
    use std::time::{Duration, Instant};

    use super::{
        Departure, Known, Ledger, PATIENCE, Received, SILENCE, Socket, Source, WAITING,
        canonical_addr, unspecified_for,
    };

    #[allow(clippy::unnecessary_wraps)] // it is compared with what `next` returns
    fn kernel(tag: u64, system: i64, source: Source) -> Option<Known> {
        Some(Known {
            tag,
            before: i64::try_from(tag).unwrap_or(0),
            kernel: Some((system, source)),
        })
    }

    /// Takes in that the datagram with `tag` was sent; its own stamp is the
    /// tag, so that a mix-up of datagrams shows in either number.
    fn send(ledger: &mut Ledger, tag: u64) {
        ledger.sent(Some(tag), i64::try_from(tag).unwrap_or(0));
    }

    /// Both reports of the datagram with `key`, with stamps that tell the
    /// key and the kind.
    fn report(ledger: &mut Ledger, key: u32) {
        ledger.scheduled(key, 1_000 + i64::from(key));
        ledger.delivered(key, 2_000 + i64::from(key));
    }

    #[test]
    fn a_report_goes_to_the_datagram_with_its_number() {
        let mut ledger = Ledger::new(true);
        for tag in [70, 71, 72] {
            send(&mut ledger, tag);
        }
        assert_eq!(ledger.next(), None);
        // The device hands the second datagram on before the first.
        ledger.scheduled(0, 1_000);
        ledger.scheduled(1, 1_001);
        assert_eq!(ledger.next(), None);
        ledger.delivered(1, 2_001);
        ledger.delivered(0, 2_000);
        report(&mut ledger, 2);
        assert_eq!(ledger.next(), kernel(71, 2_001, Source::Kernel));
        assert_eq!(ledger.next(), kernel(70, 2_000, Source::Kernel));
        assert_eq!(ledger.next(), kernel(72, 2_002, Source::Kernel));
        assert_eq!(ledger.next(), None);
        assert_eq!(ledger.decided, Some(Source::Kernel));
    }

    #[test]
    fn a_failed_send_that_used_up_a_number_shifts_the_numbers_after_it() {
        let mut ledger = Ledger::new(true);
        send(&mut ledger, 70);
        ledger.failed();
        send(&mut ledger, 71);
        send(&mut ledger, 72);
        // The kernel gave the failed send the number 1.
        for key in [0, 2, 3] {
            report(&mut ledger, key);
        }
        assert_eq!(ledger.next(), kernel(70, 2_000, Source::Kernel));
        assert_eq!(ledger.next(), kernel(71, 2_002, Source::Kernel));
        assert_eq!(ledger.next(), kernel(72, 2_003, Source::Kernel));
        // The numbers go on from there.
        send(&mut ledger, 73);
        report(&mut ledger, 4);
        assert_eq!(ledger.next(), kernel(73, 2_004, Source::Kernel));
    }

    #[test]
    fn a_failed_send_that_used_up_no_number_shifts_nothing() {
        let mut ledger = Ledger::new(true);
        send(&mut ledger, 70);
        ledger.failed();
        send(&mut ledger, 71);
        send(&mut ledger, 72);
        for key in [0, 1, 2] {
            report(&mut ledger, key);
        }
        assert_eq!(ledger.next(), kernel(70, 2_000, Source::Kernel));
        assert_eq!(ledger.next(), kernel(71, 2_001, Source::Kernel));
        assert_eq!(ledger.next(), kernel(72, 2_002, Source::Kernel));
        // The doubt is over: a later number is taken at its word.
        send(&mut ledger, 73);
        send(&mut ledger, 74);
        report(&mut ledger, 4);
        assert_eq!(ledger.next(), kernel(74, 2_004, Source::Kernel));
        assert_eq!(ledger.next(), None);
    }

    #[test]
    fn a_datagram_that_never_reached_the_queue_is_passed_over() {
        let mut ledger = Ledger::new(true);
        for tag in [70, 71, 72] {
            send(&mut ledger, tag);
        }
        report(&mut ledger, 0);
        report(&mut ledger, 2);
        assert_eq!(ledger.next(), kernel(70, 2_000, Source::Kernel));
        assert_eq!(ledger.next(), kernel(72, 2_002, Source::Kernel));
        assert_eq!(ledger.next(), None);
        assert_eq!(ledger.waiting, 0);
    }

    #[test]
    fn a_device_that_stamps_nothing_gets_the_stamps_of_the_queue() {
        let mut ledger = Ledger::new(true);
        for key in 0..=PATIENCE {
            send(&mut ledger, 70 + u64::from(key));
            assert_eq!(ledger.next(), None);
            ledger.scheduled(key, 1_000 + i64::from(key));
        }
        assert_eq!(ledger.decided, Some(Source::Scheduler));
        for key in 0..=PATIENCE {
            let tag = 70 + u64::from(key);
            assert_eq!(
                ledger.next(),
                kernel(tag, 1_000 + i64::from(key), Source::Scheduler)
            );
        }
        // From now on a stamp of the queue is handed out as it comes.
        send(&mut ledger, 90);
        ledger.scheduled(PATIENCE + 1, 5_000);
        assert_eq!(ledger.next(), kernel(90, 5_000, Source::Scheduler));
    }

    #[test]
    fn a_kernel_that_reports_nothing_gets_the_program_s_stamps() {
        let mut ledger = Ledger::new(true);
        let silence = SILENCE as u64;
        for tag in 0..=silence {
            ledger.quiet();
            assert_eq!(ledger.next(), None);
            send(&mut ledger, tag);
        }
        // The queue of reports is found empty with that many sent.
        ledger.quiet();
        assert_eq!(ledger.decided, Some(Source::Program));
        for tag in 0..=silence {
            let before = i64::try_from(tag).unwrap_or(0);
            assert_eq!(
                ledger.next(),
                Some(Known {
                    tag,
                    before,
                    kernel: None
                })
            );
        }
        send(&mut ledger, 500);
        assert!(
            ledger
                .next()
                .is_some_and(|known| known.tag == 500 && known.kernel.is_none())
        );
        // If the kernel does report later, its numbers still fit: it counted
        // every datagram in the meantime.
        ledger.delivered(0, 1);
        send(&mut ledger, 501);
        let key = u32::try_from(silence).unwrap_or(0) + 2;
        report(&mut ledger, key);
        assert_eq!(
            ledger.next(),
            kernel(501, 2_000 + i64::from(key), Source::Kernel)
        );
    }

    #[test]
    fn datagrams_whose_reports_are_not_read_yet_do_not_count_as_unreported() {
        // The caller sends many datagrams before it reads any report. The
        // reports are in the kernel's queue all along, which was never found
        // empty.
        let mut ledger = Ledger::new(true);
        for tag in 0..60 {
            send(&mut ledger, tag);
        }
        assert_eq!(ledger.decided, None);
        for key in 0..60 {
            report(&mut ledger, key);
        }
        ledger.quiet();
        for key in 0..60u32 {
            assert_eq!(
                ledger.next(),
                kernel(u64::from(key), 2_000 + i64::from(key), Source::Kernel)
            );
        }
    }

    #[test]
    fn without_reports_a_datagram_has_the_program_s_stamp_at_once() {
        let mut ledger = Ledger::new(false);
        send(&mut ledger, 70);
        assert_eq!(
            ledger.next(),
            Some(Known {
                tag: 70,
                before: 70,
                kernel: None
            })
        );
    }

    #[test]
    fn more_datagrams_than_can_wait_push_out_the_oldest_and_the_rest_still_match() {
        let mut ledger = Ledger::new(true);
        send(&mut ledger, 1);
        report(&mut ledger, 0);
        assert!(ledger.next().is_some());
        let count = 2 * WAITING;
        for tag in 0..count {
            send(&mut ledger, 100 + tag as u64);
        }
        // Only the last ten are reported.
        for step in count - 10..count {
            report(&mut ledger, u32::try_from(1 + step).unwrap_or(0));
        }
        for step in count - 10..count {
            let key = i64::try_from(1 + step).unwrap_or(0);
            assert_eq!(
                ledger.next(),
                kernel(100 + step as u64, 2_000 + key, Source::Kernel)
            );
        }
        assert_eq!(ledger.next(), None);
    }

    fn loopback() -> SocketAddr {
        SocketAddr::from(([127, 0, 0, 1], 0))
    }

    /// Receives one datagram, waiting up to two seconds for it.
    fn receive(socket: &mut Socket, buffer: &mut [u8]) -> Received {
        let give_up = Instant::now() + Duration::from_secs(2);
        loop {
            if let Some(received) = socket.receive(buffer).expect("receiving") {
                return received;
            }
            assert!(Instant::now() < give_up, "no datagram within two seconds");
            socket.wait(50).expect("waiting");
        }
    }

    /// Collects departures until there are `count` or none has come for
    /// two seconds.
    fn departures(socket: &mut Socket, count: usize) -> Vec<Departure> {
        let mut found = Vec::new();
        let mut give_up = Instant::now() + Duration::from_secs(2);
        while found.len() < count && Instant::now() < give_up {
            match socket.departure().expect("reading departures") {
                Some(departure) => {
                    found.push(departure);
                    give_up = Instant::now() + Duration::from_secs(2);
                }
                None => {
                    socket.wait(20).expect("waiting");
                }
            }
        }
        found
    }

    /// Takes the departures that are known now.
    fn known(socket: &mut Socket, into: &mut Vec<Departure>) {
        while let Some(departure) = socket.departure().expect("reading departures") {
            into.push(departure);
        }
    }

    #[test]
    fn every_datagram_arrives_with_a_stamp_and_reports_its_departure() {
        let mut sender = Socket::bind(loopback()).expect("a socket");
        let mut listener = Socket::bind(loopback()).expect("a socket");
        let to = listener.address().expect("an address");
        let mut buffer = [0u8; 64];
        let mut left = Vec::new();
        for tag in 0..100u64 {
            let sent = sender
                .send_to(&tag.to_le_bytes(), to, tag)
                .expect("sending");
            let got = receive(&mut listener, &mut buffer);
            assert_eq!(buffer.get(..got.length), Some(&tag.to_le_bytes()[..]));
            assert_eq!(got.from, sender.address().expect("an address"));
            // However the stamps were made, the datagram did not arrive
            // before it was sent.
            assert!(got.read >= sent.before);
            assert!(got.arrival.time + got.arrival.error >= sent.before);
            known(&mut sender, &mut left);
        }
        let missing = 100 - left.len();
        left.extend(departures(&mut sender, missing));
        let tags: Vec<u64> = left.iter().map(|departure| departure.tag).collect();
        assert_eq!(tags, (0..100).collect::<Vec<u64>>());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn the_kernel_stamps_bracket_the_transit_tighter_than_the_program_does() {
        let mut sender = Socket::bind(loopback()).expect("a socket");
        let mut listener = Socket::bind(loopback()).expect("a socket");
        assert_eq!(listener.arrivals(), Source::Kernel);
        let to = listener.address().expect("an address");
        let mut buffer = [0u8; 64];
        let mut exchanged = Vec::new();
        let mut left = Vec::new();
        for tag in 0..200u64 {
            let sent = sender
                .send_to(&tag.to_le_bytes(), to, tag)
                .expect("sending");
            exchanged.push((sent, receive(&mut listener, &mut buffer)));
            known(&mut sender, &mut left);
        }
        let missing = 200 - left.len();
        left.extend(departures(&mut sender, missing));
        assert_eq!(left.len(), 200);
        // On the loopback interface the device stamps what it is handed.
        assert_eq!(sender.departures(), Some(Source::Kernel));
        let mut transits = Vec::new();
        for ((sent, got), departure) in exchanged.iter().zip(&left) {
            let (arrival, departure) = (got.arrival, departure.stamp);
            assert_eq!(
                (arrival.source, departure.source),
                (Source::Kernel, Source::Kernel)
            );
            let unsure = arrival.error + departure.error;
            // In order: the program's stamp before the send, the departure,
            // the arrival, the program's stamp after the receive. The
            // program's two stamps therefore err toward a longer transit.
            assert!(
                sent.before <= departure.time + departure.error,
                "{sent:?} {departure:?}"
            );
            assert!(
                departure.time <= arrival.time + unsure,
                "{departure:?} {arrival:?}"
            );
            assert!(arrival.time <= got.read + arrival.error, "{got:?}");
            transits.push(arrival.time - departure.time);
        }
        // The loopback interface hands a datagram over in well under a
        // microsecond. Half of the datagrams at least are not interrupted on
        // the way, whatever else the host does.
        transits.sort_unstable();
        let median = transits
            .get(transits.len() / 2)
            .copied()
            .unwrap_or(i64::MAX);
        assert!(median < 100_000, "median transit {median} ns");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn departures_go_to_their_datagrams_when_several_are_under_way() {
        let mut sender = Socket::bind(loopback()).expect("a socket");
        let mut listener = Socket::bind(loopback()).expect("a socket");
        let to = listener.address().expect("an address");
        // Forty datagrams are sent before any report is read. They are a
        // third of a millisecond apart, far more than any stamp is unsure
        // by, so a departure given to the wrong datagram lies outside the
        // time between that datagram's send and its arrival.
        let mut sent = Vec::new();
        for number in 0..40u64 {
            let tag = 1_000 + 7 * number;
            sent.push((
                tag,
                sender
                    .send_to(&tag.to_le_bytes(), to, tag)
                    .expect("sending"),
            ));
            std::thread::sleep(Duration::from_micros(300));
        }
        let mut buffer = [0u8; 64];
        let arrivals: Vec<Received> = (0..40)
            .map(|_| receive(&mut listener, &mut buffer))
            .collect();
        let left = departures(&mut sender, 40);
        assert_eq!(left.len(), 40);
        for (((tag, sent), arrival), departure) in sent.iter().zip(&arrivals).zip(&left) {
            assert_eq!(departure.tag, *tag);
            let stamp = departure.stamp;
            assert!(
                stamp.time + stamp.error >= sent.before,
                "{tag}: {stamp:?} {sent:?}"
            );
            assert!(
                stamp.time - stamp.error <= arrival.arrival.time + arrival.arrival.error,
                "{tag}: {stamp:?} {arrival:?}"
            );
            assert!(stamp.error < 100_000, "{stamp:?}");
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn the_kernel_stamps_datagrams_of_the_newer_internet_protocol_too() {
        // The reports of departures come in another kind of control message
        // there. A host without the protocol has nothing to test.
        let loopback = SocketAddr::from(([0, 0, 0, 0, 0, 0, 0, 1], 0));
        let (Ok(mut sender), Ok(mut listener)) = (Socket::bind(loopback), Socket::bind(loopback))
        else {
            return;
        };
        let to = listener.address().expect("an address");
        let mut buffer = [0u8; 64];
        let mut left = Vec::new();
        for tag in 0..10u64 {
            sender
                .send_to(&tag.to_le_bytes(), to, tag)
                .expect("sending");
            let got = receive(&mut listener, &mut buffer);
            assert_eq!(got.arrival.source, Source::Kernel);
            assert_eq!(got.from, sender.address().expect("an address"));
            known(&mut sender, &mut left);
        }
        let missing = 10 - left.len();
        left.extend(departures(&mut sender, missing));
        let tags: Vec<u64> = left.iter().map(|departure| departure.tag).collect();
        assert_eq!(tags, (0..10).collect::<Vec<u64>>());
        assert!(
            left.iter()
                .all(|departure| departure.stamp.source == Source::Kernel)
        );
    }

    #[test]
    fn untagged_sends_preserve_keys_without_reporting_departures() {
        let mut ledger = Ledger::new(true);
        send(&mut ledger, 10);
        ledger.sent(None, 11);
        ledger.sent(None, 12);
        send(&mut ledger, 13);
        for key in 0..4 {
            report(&mut ledger, key);
        }
        assert_eq!(ledger.next(), kernel(10, 2_000, Source::Kernel));
        assert_eq!(ledger.next(), kernel(13, 2_003, Source::Kernel));
        assert_eq!(ledger.next(), None);
        assert_eq!(ledger.waiting, 0);
    }

    #[test]
    fn canonical_addr_folds_ipv4_mapped_ipv6_and_unspecified_for_matches_family() {
        let v4: SocketAddr = "127.0.0.1:5000".parse().expect("v4");
        let mapped: SocketAddr = "[::ffff:127.0.0.1]:5000".parse().expect("mapped");
        let v6: SocketAddr = "[::1]:5000".parse().expect("v6");
        assert_eq!(canonical_addr(v4), v4);
        assert_eq!(canonical_addr(mapped), v4);
        assert_eq!(canonical_addr(v6), v6);
        assert!(unspecified_for(&[]).is_ipv4());
        assert!(unspecified_for(&[v4]).is_ipv4());
        assert!(unspecified_for(&[v4, v6]).is_ipv6());
        assert!(unspecified_for(&[mapped]).is_ipv6());
    }

    #[test]
    fn transient_send_error_distinguishes_eacces_from_eperm_and_addr_not_available() {
        use std::io;

        use super::{is_restricted_send_error, is_transient_send_error};
        let would_block = io::Error::from(io::ErrorKind::WouldBlock);
        assert!(is_transient_send_error(&would_block));
        assert!(!is_restricted_send_error(&would_block));
        assert!(is_transient_send_error(&io::Error::from(
            io::ErrorKind::NetworkUnreachable
        )));
        assert!(is_transient_send_error(&io::Error::from(
            io::ErrorKind::ConnectionRefused
        )));
        let addr_unavail = io::Error::from(io::ErrorKind::AddrNotAvailable);
        assert!(is_transient_send_error(&addr_unavail));
        assert!(is_restricted_send_error(&addr_unavail));
        #[cfg(unix)]
        {
            let enobufs = io::Error::from_raw_os_error(libc::ENOBUFS);
            assert!(is_transient_send_error(&enobufs));
            assert!(!is_restricted_send_error(&enobufs));
            let eperm = io::Error::from_raw_os_error(libc::EPERM);
            assert!(is_transient_send_error(&eperm));
            assert!(is_restricted_send_error(&eperm));
            let eaddrnotavail = io::Error::from_raw_os_error(libc::EADDRNOTAVAIL);
            assert!(is_transient_send_error(&eaddrnotavail));
            assert!(is_restricted_send_error(&eaddrnotavail));
            let eacces = io::Error::from_raw_os_error(libc::EACCES);
            assert!(!is_transient_send_error(&eacces));
            assert!(!is_restricted_send_error(&eacces));
        }
        let generic_perm = io::Error::from(io::ErrorKind::PermissionDenied);
        assert!(!is_transient_send_error(&generic_perm));
        assert!(!is_restricted_send_error(&generic_perm));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_send_that_fails_leaves_the_later_departures_with_their_datagrams() {
        let mut sender = Socket::bind(loopback()).expect("a socket");
        let mut listener = Socket::bind(loopback()).expect("a socket");
        let to = listener.address().expect("an address");
        let mut buffer = [0u8; 64];
        let mut exchanged = Vec::new();
        for tag in 0..6u64 {
            if tag == 2 || tag == 3 {
                // More than a datagram can hold.
                let too_long = vec![0u8; 70_000];
                assert!(sender.send_to(&too_long, to, 999).is_err());
            }
            let sent = sender
                .send_to(&tag.to_le_bytes(), to, tag)
                .expect("sending");
            exchanged.push((tag, sent, receive(&mut listener, &mut buffer)));
            std::thread::sleep(Duration::from_micros(300));
        }
        let left = departures(&mut sender, 6);
        assert_eq!(left.len(), 6);
        for ((tag, sent, received), departure) in exchanged.iter().zip(&left) {
            assert_eq!(departure.tag, *tag);
            let stamp = departure.stamp;
            assert!(stamp.time + stamp.error >= sent.before, "{tag}: {stamp:?}");
            assert!(stamp.time - stamp.error <= received.arrival.time + received.arrival.error);
        }
    }
}
