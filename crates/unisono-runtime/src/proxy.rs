// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A proxy that delays, drops, pauses, reorders and duplicates datagrams.
//!
//! It is equipment for tests: two programs that would talk over a network
//! talk through a [`Proxy`] on one host, and the proxy does to their
//! datagrams what a network might. What it does to each datagram is decided
//! by a seed and by the order in which the datagrams arrive, so a test that
//! fails can be run again and fails the same way.
//!
//! # What happens to a datagram
//!
//! Each direction has an [`Impairment`] and a sequence of random numbers of
//! its own. For every datagram that arrives, [`Direction::fate`] draws the
//! same count of numbers and decides, in this order:
//!
//! - whether the datagram starts a **pause** of the direction, which lasts
//!   `pause_length` from its arrival. A datagram that arrives while a pause
//!   lasts, the one that started it included, is delivered at the end of the
//!   pause at the earliest;
//! - whether it is **lost**, and then nothing more happens;
//! - when it is delivered: `delay` after its arrival, plus up to `jitter`,
//!   plus `held_back` if it is one of those to be **reordered**, which lets
//!   the datagrams that arrive within that time overtake it;
//! - whether it is **duplicated**, and then a second copy is delivered with
//!   a jitter of its own.
//!
//! The proxy delivers a datagram no earlier than the decided time, and as
//! soon after it as the host's timers allow, which is within a millisecond
//! or two on an idle host.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::JoinHandle;

use crate::clock;

/// What a direction of a proxy does to datagrams. Times are in nanoseconds
/// and probabilities are for each datagram by itself.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Impairment {
    /// How long every datagram is held.
    pub delay: i64,
    /// The largest additional time a datagram is held; the time is drawn
    /// evenly from zero up to it.
    pub jitter: i64,
    /// The probability that a datagram is lost.
    pub loss: f64,
    /// The probability that a datagram is delivered twice.
    pub duplication: f64,
    /// The probability that a datagram is held back so that later ones
    /// overtake it.
    pub reordering: f64,
    /// How much longer such a datagram is held.
    pub held_back: i64,
    /// The probability that a datagram starts a pause.
    pub pause: f64,
    /// How long a pause lasts.
    pub pause_length: i64,
}

impl Impairment {
    /// Every datagram is passed on at once.
    pub const NONE: Impairment = Impairment {
        delay: 0,
        jitter: 0,
        loss: 0.0,
        duplication: 0.0,
        reordering: 0.0,
        held_back: 0,
        pause: 0.0,
        pause_length: 0,
    };
}

/// When the copies of a datagram are delivered: none if it is lost, one, or
/// two if it is duplicated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fate {
    /// The time of the first copy.
    pub first: Option<i64>,
    /// The time of the second copy.
    pub second: Option<i64>,
}

/// A sequence of numbers that is the same for the same seed (the `SplitMix64`
/// generator).
#[derive(Clone, Debug)]
struct Sequence(u64);

impl Sequence {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number from zero up to, but not including, one.
    fn unit(&mut self) -> f64 {
        // The top 53 bits, which a float holds exactly.
        #[allow(clippy::cast_precision_loss)]
        let unit = (self.next() >> 11) as f64 / 9_007_199_254_740_992.0;
        unit
    }
}

/// One direction of a proxy: its impairment and its random numbers.
#[derive(Clone, Debug)]
pub struct Direction {
    impairment: Impairment,
    sequence: Sequence,
    paused_until: i64,
}

impl Direction {
    /// A direction with this impairment, whose decisions follow from `seed`.
    #[must_use]
    pub fn new(impairment: Impairment, seed: u64) -> Direction {
        Direction {
            impairment,
            sequence: Sequence(seed),
            paused_until: i64::MIN,
        }
    }

    /// What becomes of the next datagram, which arrives at `arrival`.
    pub fn fate(&mut self, arrival: i64) -> Fate {
        let set = self.impairment;
        // The same six draws for every datagram, whatever becomes of it, so
        // that the fate of one does not shift the numbers of the next.
        let starts_pause = self.sequence.unit() < set.pause;
        let lost = self.sequence.unit() < set.loss;
        let reordered = self.sequence.unit() < set.reordering;
        let duplicated = self.sequence.unit() < set.duplication;
        let jitters = [self.sequence.unit(), self.sequence.unit()];
        if starts_pause {
            self.paused_until = self
                .paused_until
                .max(arrival.saturating_add(set.pause_length));
        }
        if lost {
            return Fate {
                first: None,
                second: None,
            };
        }
        let paused_until = self.paused_until;
        let time = |jitter: f64| {
            // A jitter of nanoseconds is far inside what a float holds.
            #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
            let extra = (set.jitter as f64 * jitter) as i64;
            let held = if reordered { set.held_back } else { 0 };
            arrival
                .saturating_add(set.delay)
                .saturating_add(extra)
                .saturating_add(held)
                .max(paused_until)
        };
        let [first, second] = jitters;
        Fate {
            first: Some(time(first)),
            second: duplicated.then(|| time(second)),
        }
    }
}

/// A datagram that waits in the proxy to be delivered.
struct Held {
    forward: bool,
    bytes: Vec<u8>,
}

/// A running proxy between a first party, which sends to [`Proxy::near`],
/// and a second party at a fixed address.
///
/// The proxy passes datagrams from the first party on to the second, from
/// its other socket, and passes what the second party sends back to that
/// socket on to whoever sent to [`Proxy::near`] last. Dropping the proxy
/// stops it.
pub struct Proxy {
    near: SocketAddr,
    far: SocketAddr,
    stop: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
}

impl Proxy {
    /// Starts a proxy in front of the party at `target`, on the loopback
    /// interface. Datagrams toward `target` are impaired by `forward`, those
    /// from it by `backward`, and all decisions follow from `seed`.
    ///
    /// # Errors
    ///
    /// What the system says when the sockets or the thread cannot be made.
    pub fn start(
        target: SocketAddr,
        forward: Impairment,
        backward: Impairment,
        seed: u64,
    ) -> io::Result<Proxy> {
        let loopback: SocketAddr = if target.is_ipv4() {
            SocketAddr::from(([127, 0, 0, 1], 0))
        } else {
            SocketAddr::from(([0, 0, 0, 0, 0, 0, 0, 1], 0))
        };
        let front = UdpSocket::bind(loopback)?;
        let back = UdpSocket::bind(loopback)?;
        front.set_nonblocking(true)?;
        back.set_nonblocking(true)?;
        let near = front.local_addr()?;
        let far = back.local_addr()?;
        let stop = Arc::new(AtomicBool::new(false));
        let stopping = Arc::clone(&stop);
        // The two directions get seeds that differ, from the one seed.
        let mut seeds = Sequence(seed);
        let running = Running {
            front,
            back,
            target,
            client: None,
            forward: Direction::new(forward, seeds.next()),
            backward: Direction::new(backward, seeds.next()),
            waiting: BinaryHeap::new(),
            held: Vec::new(),
            free: Vec::new(),
            count: 0,
            buffer: vec![0; 65_536],
        };
        let thread = std::thread::Builder::new()
            .name("unisono-proxy".into())
            .spawn(move || running.run(&stopping))?;
        Ok(Proxy {
            near,
            far,
            stop,
            thread: Some(thread),
        })
    }

    /// The address that the first party sends to.
    #[must_use]
    pub fn near(&self) -> SocketAddr {
        self.near
    }

    /// The address that the second party sees datagrams come from, and
    /// sends its own to.
    #[must_use]
    pub fn far(&self) -> SocketAddr {
        self.far
    }
}

impl Drop for Proxy {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
        if let Some(thread) = self.thread.take() {
            // A proxy thread that panicked has nothing more to say here.
            let _ = thread.join();
        }
    }
}

/// How long the proxy's thread sleeps at most before it looks whether it is
/// to stop, in milliseconds.
const LONGEST_SLEEP: i64 = 20;

/// The state of a proxy's thread.
struct Running {
    front: UdpSocket,
    back: UdpSocket,
    target: SocketAddr,
    /// Who sent to the front last.
    client: Option<SocketAddr>,
    forward: Direction,
    backward: Direction,
    /// Times of delivery with the number of the held datagram, earliest
    /// first; equal times in the order the datagrams arrived.
    waiting: BinaryHeap<Reverse<(i64, u64, usize)>>,
    /// The held datagrams, by their place; a delivered one leaves `None`.
    held: Vec<Option<(Held, u8)>>,
    /// Empty places in `held` available for reuse without growing the vector.
    free: Vec<usize>,
    count: u64,
    /// Room for the largest datagram there is.
    buffer: Vec<u8>,
}

impl Running {
    /// Stores a held datagram in a freed slot if one is available, or appends
    /// a new slot, and returns its index.
    fn store_held(&mut self, item: (Held, u8)) -> usize {
        if let Some(place) = self.free.pop()
            && let Some(slot) = self.held.get_mut(place)
        {
            *slot = Some(item);
            return place;
        }
        let place = self.held.len();
        self.held.push(Some(item));
        place
    }

    /// Takes in the datagram in the first `length` bytes of the buffer,
    /// which arrived just now.
    fn take(&mut self, forward: bool, length: usize) {
        let now = clock::raw();
        let fate = if forward {
            self.forward.fate(now)
        } else {
            self.backward.fate(now)
        };
        let copies = u8::from(fate.first.is_some()) + u8::from(fate.second.is_some());
        if copies == 0 {
            return;
        }
        let bytes = self.buffer.get(..length).unwrap_or(&[]).to_vec();
        let place = self.store_held((Held { forward, bytes }, copies));
        for time in [fate.first, fate.second].into_iter().flatten() {
            self.waiting.push(Reverse((time, self.count, place)));
            self.count += 1;
        }
    }

    /// Receives everything that waits at both sockets.
    fn receive(&mut self) {
        while let Ok((length, from)) = self.front.recv_from(&mut self.buffer) {
            self.client = Some(from);
            self.take(true, length);
        }
        while let Ok((length, from)) = self.back.recv_from(&mut self.buffer) {
            if from == self.target {
                self.take(false, length);
            }
        }
    }

    /// Delivers what is due, and returns the time of the next delivery.
    fn deliver(&mut self) -> Option<i64> {
        loop {
            let Reverse((time, _, place)) = self.waiting.peek().copied()?;
            if time > clock::raw() {
                return Some(time);
            }
            self.waiting.pop();
            let Some(slot) = self.held.get_mut(place) else {
                continue;
            };
            let Some((held, copies)) = slot.as_mut() else {
                continue;
            };
            // A datagram that cannot be sent is one more that is lost.
            let _ = if held.forward {
                self.back.send_to(&held.bytes, self.target)
            } else if let Some(client) = self.client {
                self.front.send_to(&held.bytes, client)
            } else {
                Ok(0)
            };
            *copies = copies.saturating_sub(1);
            let delivered = *copies == 0;
            if delivered {
                *slot = None;
                self.free.push(place);
            }
        }
    }

    fn run(mut self, stop: &AtomicBool) {
        while !stop.load(Ordering::Relaxed) {
            self.receive();
            let next = self.deliver();
            if self.waiting.is_empty() {
                // Nothing is held, so the places can be used from the start.
                self.held.clear();
                self.free.clear();
            }
            let sleep = next.map_or(LONGEST_SLEEP * 1_000_000, |time| {
                time.saturating_sub(clock::raw())
            });
            sys::wait(
                &self.front,
                &self.back,
                sleep.clamp(0, LONGEST_SLEEP * 1_000_000),
            );
        }
    }
}

#[cfg(unix)]
mod sys {
    use std::net::UdpSocket;
    use std::os::fd::AsRawFd;

    /// Waits until one of the sockets can be read, for at most `nanos`
    /// nanoseconds.
    pub(super) fn wait(front: &UdpSocket, back: &UdpSocket, nanos: i64) {
        let mut polls = [front, back].map(|socket| libc::pollfd {
            fd: socket.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        });
        // Whole milliseconds, rounded down, so that the wait ends before a
        // delivery is due; the rest is slept away in one short step.
        let milliseconds = libc::c_int::try_from(nanos / 1_000_000).unwrap_or(0);
        if milliseconds == 0 {
            if nanos > 0 {
                std::thread::sleep(std::time::Duration::from_nanos(
                    u64::try_from(nanos).unwrap_or(0),
                ));
            }
            return;
        }
        // SAFETY: `polls` is two valid `pollfd`, and the count says two. An
        // error leaves nothing to do but to look again.
        unsafe { libc::poll(polls.as_mut_ptr(), 2, milliseconds) };
    }
}

#[cfg(not(unix))]
mod sys {
    use std::net::UdpSocket;

    /// Sleeps a millisecond: this system has no call here to wait for two
    /// sockets at once.
    pub(super) fn wait(_front: &UdpSocket, _back: &UdpSocket, _nanos: i64) {
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
}

#[cfg(test)]
mod tests {
    use std::net::{SocketAddr, UdpSocket};
    use std::time::{Duration, Instant};

    use super::{Direction, Fate, Impairment, Proxy};
    use crate::clock;

    const MILLISECOND: i64 = 1_000_000;
    const DATAGRAMS: u32 = 100_000;

    /// The fates of datagrams that arrive a millisecond apart.
    fn fates(impairment: Impairment, seed: u64) -> Vec<(i64, Fate)> {
        let mut direction = Direction::new(impairment, seed);
        (0..i64::from(DATAGRAMS))
            .map(|number| {
                let arrival = number * MILLISECOND;
                (arrival, direction.fate(arrival))
            })
            .collect()
    }

    fn share(count: usize) -> f64 {
        f64::from(u32::try_from(count).unwrap_or(u32::MAX)) / f64::from(DATAGRAMS)
    }

    #[test]
    fn without_impairment_every_datagram_is_passed_on_at_once() {
        for (arrival, fate) in fates(Impairment::NONE, 1) {
            assert_eq!(
                fate,
                Fate {
                    first: Some(arrival),
                    second: None
                }
            );
        }
    }

    #[test]
    fn losses_and_duplicates_come_at_their_rates() {
        let impairment = Impairment {
            loss: 0.1,
            duplication: 0.05,
            ..Impairment::NONE
        };
        let fates = fates(impairment, 7);
        // Of 100,000 datagrams the share that is lost has a standard
        // deviation of 0.00095, and the share that is duplicated, among the
        // 90 % that are not lost, one of 0.00067: the bounds are four of
        // them.
        let lost = share(
            fates
                .iter()
                .filter(|(_, fate)| fate.first.is_none())
                .count(),
        );
        assert!((lost - 0.1).abs() < 0.004, "lost {lost}");
        let twice = share(
            fates
                .iter()
                .filter(|(_, fate)| fate.second.is_some())
                .count(),
        );
        assert!((twice - 0.045).abs() < 0.003, "duplicated {twice}");
        // A lost datagram has no second copy either.
        assert!(
            fates
                .iter()
                .all(|(_, fate)| fate.first.is_some() || fate.second.is_none())
        );
    }

    #[test]
    fn delays_lie_between_the_delay_and_the_delay_plus_the_jitter() {
        let impairment = Impairment {
            delay: 3 * MILLISECOND,
            jitter: 2 * MILLISECOND,
            duplication: 0.5,
            ..Impairment::NONE
        };
        let fates = fates(impairment, 3);
        let mut sum = 0i64;
        let mut copies = 0i64;
        for (arrival, fate) in &fates {
            for time in [fate.first, fate.second].into_iter().flatten() {
                let held = time - arrival;
                assert!(
                    (3 * MILLISECOND..5 * MILLISECOND).contains(&held),
                    "held {held}"
                );
                sum += held;
                copies += 1;
            }
        }
        // The jitter is spread evenly, so the mean is the delay plus half
        // of it; the mean of 150,000 draws is within 0.006 ms of that at
        // four standard deviations.
        let mean = sum / copies;
        assert!(
            (mean - 4 * MILLISECOND).abs() < MILLISECOND / 100,
            "mean {mean}"
        );
    }

    #[test]
    fn a_reordered_datagram_is_overtaken_by_those_that_arrive_while_it_is_held() {
        let impairment = Impairment {
            reordering: 0.2,
            held_back: 5 * MILLISECOND + MILLISECOND / 2,
            ..Impairment::NONE
        };
        let fates = fates(impairment, 5);
        let held = share(
            fates
                .iter()
                .filter(|(arrival, fate)| fate.first != Some(*arrival))
                .count(),
        );
        // Four standard deviations of the share are 0.005.
        assert!((held - 0.2).abs() < 0.005, "held back {held}");
        // A datagram held back for five and a half milliseconds is delivered
        // after the five that arrive in that time, unless they are held too.
        let overtaken = fates
            .windows(2)
            .filter(|pair| pair[0].1.first > pair[1].1.first)
            .count();
        // That is the case for a held datagram followed by one that is not:
        // 0.2 * 0.8 of all pairs.
        assert!(
            (share(overtaken) - 0.16).abs() < 0.005,
            "overtaken {overtaken}"
        );
    }

    #[test]
    fn a_pause_holds_what_arrives_during_it_and_keeps_the_order() {
        let impairment = Impairment {
            pause: 0.01,
            pause_length: 20 * MILLISECOND,
            ..Impairment::NONE
        };
        let fates = fates(impairment, 9);
        let times: Vec<i64> = fates.iter().filter_map(|(_, fate)| fate.first).collect();
        assert!(times.windows(2).all(|pair| pair[0] <= pair[1]));
        // A datagram is held if one of the twenty up to and including it
        // started a pause: 1 - 0.99^20 = 0.182. Held datagrams come in runs
        // of twenty, so the share is as sure as that of 5,000 independent
        // ones, and four standard deviations are 0.022.
        let held = share(
            fates
                .iter()
                .filter(|(arrival, fate)| fate.first != Some(*arrival))
                .count(),
        );
        assert!((held - 0.182).abs() < 0.022, "held {held}");
        // Nothing is held longer than a pause.
        assert!(fates.iter().all(|(arrival, fate)| {
            fate.first
                .is_some_and(|time| time - arrival <= 20 * MILLISECOND)
        }));
    }

    #[test]
    fn the_same_seed_gives_the_same_fates_and_another_seed_others() {
        let impairment = Impairment {
            delay: MILLISECOND,
            jitter: MILLISECOND,
            loss: 0.2,
            duplication: 0.2,
            reordering: 0.2,
            held_back: MILLISECOND,
            pause: 0.01,
            pause_length: 5 * MILLISECOND,
        };
        assert_eq!(fates(impairment, 42), fates(impairment, 42));
        assert_ne!(fates(impairment, 42), fates(impairment, 43));
    }

    /// A socket on the loopback interface that waits up to a twentieth of a
    /// second for a datagram.
    fn party() -> UdpSocket {
        let socket = UdpSocket::bind("127.0.0.1:0").expect("a socket on the loopback interface");
        socket
            .set_read_timeout(Some(Duration::from_millis(50)))
            .expect("a timeout");
        socket
    }

    /// Receives numbered datagrams until `count` have come, for at most
    /// twenty seconds, and then for a twentieth of a second more to see
    /// whether one too many comes. Returns the numbers with the raw clock
    /// at each.
    fn collect(socket: &UdpSocket, count: usize) -> Vec<(u32, i64, SocketAddr)> {
        let mut seen = Vec::new();
        let mut buffer = [0u8; 64];
        let give_up = Instant::now() + Duration::from_secs(20);
        while Instant::now() < give_up {
            let Ok((length, from)) = socket.recv_from(&mut buffer) else {
                if seen.len() >= count {
                    break;
                }
                continue;
            };
            let at = clock::raw();
            if let Some(Ok(bytes)) = buffer.get(..length).map(<[u8; 4]>::try_from) {
                seen.push((u32::from_le_bytes(bytes), at, from));
            }
        }
        seen
    }

    #[test]
    fn datagrams_pass_both_ways_and_none_before_its_delay() {
        let server = party();
        let client = party();
        let delayed = Impairment {
            delay: 3 * MILLISECOND,
            ..Impairment::NONE
        };
        let proxy = Proxy::start(
            server.local_addr().expect("an address"),
            delayed,
            Impairment::NONE,
            1,
        )
        .expect("a proxy");
        let mut sent = Vec::new();
        for number in 0..50u32 {
            sent.push(clock::raw());
            client
                .send_to(&number.to_le_bytes(), proxy.near())
                .expect("a datagram sent");
        }
        let seen = collect(&server, 50);
        let numbers: Vec<u32> = seen.iter().map(|(number, _, _)| *number).collect();
        assert_eq!(numbers, (0..50).collect::<Vec<u32>>());
        for ((_, arrived, from), sent) in seen.iter().zip(&sent) {
            // The server sees the proxy, not the client.
            assert_eq!(*from, proxy.far());
            // The clock was read before the send, so the time between the
            // readings is at least the delay.
            assert!(
                arrived - sent >= 3 * MILLISECOND,
                "after {} ns",
                arrived - sent
            );
        }
        // What the server sends to the proxy comes back to the client.
        for number in 100..110u32 {
            server
                .send_to(&number.to_le_bytes(), proxy.far())
                .expect("a datagram sent");
        }
        let back: Vec<u32> = collect(&client, 10)
            .iter()
            .map(|(number, _, _)| *number)
            .collect();
        assert_eq!(back, (100..110).collect::<Vec<u32>>());
    }

    #[test]
    fn a_proxy_does_to_datagrams_what_its_seed_says() {
        let impairment = Impairment {
            loss: 0.3,
            duplication: 0.2,
            ..Impairment::NONE
        };
        // What the direction toward the server does to 200 datagrams, by
        // the same rule the proxy uses to seed its directions.
        let mut seeds = super::Sequence(77);
        let mut direction = Direction::new(impairment, seeds.next());
        let mut expected = Vec::new();
        for number in 0..200u32 {
            let fate = direction.fate(0);
            expected.extend(fate.first.map(|_| number));
            expected.extend(fate.second.map(|_| number));
        }
        // The rates leave no doubt that both kinds occur among 200.
        assert!(expected.len() < 200 && expected.windows(2).any(|pair| pair[0] == pair[1]));

        let server = party();
        let client = party();
        let proxy = Proxy::start(
            server.local_addr().expect("an address"),
            impairment,
            Impairment::NONE,
            77,
        )
        .expect("a proxy");
        for number in 0..200u32 {
            client
                .send_to(&number.to_le_bytes(), proxy.near())
                .expect("a datagram sent");
            // A pause now and then, so that the buffer of the proxy's
            // socket cannot overflow and lose a datagram of its own accord.
            if number % 20 == 19 {
                std::thread::sleep(Duration::from_millis(2));
            }
        }
        let seen: Vec<u32> = collect(&server, expected.len())
            .iter()
            .map(|(number, _, _)| *number)
            .collect();
        assert_eq!(seen, expected);
    }

    #[test]
    fn held_slots_are_reused_while_traffic_remains_in_flight() {
        let front = party();
        let back = party();
        let target = party().local_addr().expect("an address");
        let mut running = super::Running {
            front,
            back,
            target,
            client: None,
            forward: Direction::new(
                Impairment {
                    delay: 5_000_000,
                    ..Impairment::NONE
                },
                1,
            ),
            backward: Direction::new(Impairment::NONE, 2),
            waiting: std::collections::BinaryHeap::new(),
            held: Vec::new(),
            free: Vec::new(),
            count: 0,
            buffer: vec![0; 64],
        };
        // Keep one datagram permanently in flight so `waiting` is never empty,
        // while churning through 200 immediate deliveries.
        let keep = running.store_held((
            super::Held {
                forward: true,
                bytes: vec![1],
            },
            1,
        ));
        running.waiting.push(std::cmp::Reverse((i64::MAX, 0, keep)));
        running.count = 1;
        for step in 0..200u64 {
            let place = running.store_held((
                super::Held {
                    forward: true,
                    bytes: vec![2],
                },
                1,
            ));
            running
                .waiting
                .push(std::cmp::Reverse((0, step + 1, place)));
            running.deliver();
        }
        assert!(
            running.held.len() <= 2,
            "held slots grew to {}",
            running.held.len()
        );
    }
}
