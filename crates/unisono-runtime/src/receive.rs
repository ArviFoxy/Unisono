// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The two threads of a receiver, and what passes between them.
//!
//! A receiver runs on two threads. The **network thread** owns the socket:
//! it waits for datagrams, has them stamped on arrival, sends the receiver's
//! reports and learns when they left. The **audio thread** owns everything
//! else: the receiver of the core, the frames it holds and the pump, in a
//! [`ReceiverPlayback`]. The core is not divided between the threads, so what
//! is proved about it holds as it is; the threads only pass it its inputs.
//!
//! What crosses goes through rings ([`crate::ring`]), which neither end
//! waits at:
//!
//! - to the audio thread, [`Incoming`] items: audio packets with the time of
//!   their arrival, the sender's answers to reports, and when reports left;
//! - to the network thread, the reports to send;
//! - back to the network thread, the buffers that audio packets came in.
//!
//! The buffers are made once, when the two ends are made, and go round: the
//! network thread receives a datagram into one and hands it over, and the
//! audio thread takes the samples out and hands it back. Neither thread
//! allocates or frees memory afterwards. When the audio thread does not hand
//! buffers back, as when its device stopped, the network thread has none to
//! receive into, and drops what arrives and counts it.
//!
//! The audio thread takes in at most a set number of items at the start of
//! each cycle, so the work of a cycle has a bound: that number times the
//! work of a packet, which `crates/cycle-cost` counts. A frame is played at
//! the earliest in the cycle after it arrived either way, because a cycle's
//! frames are planned at its start; taking packets in at the start of a
//! cycle loses nothing.

use std::io;
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU32, AtomicU64, Ordering};

use unisono_core::packet::{
    self, Audio, Echo, KIND_AUDIO, KIND_ECHO, Recent, Report, Request, parse_audio, parse_echo,
    write_needs, write_report, write_request,
};

use crate::asking::Asking;
use crate::audio::Playback;
use crate::clock;
use crate::network_thread::NetworkLoop;
use crate::pump::ReceiverPlayback;
use crate::ring::{Consumer, Producer, ring};
use crate::socket::{Socket, canonical_addr, is_restricted_send_error, is_transient_send_error};

/// Maximum datagrams drained in one [`ReceiverNetwork::turn`] so a burst
/// cannot starve departures, reports, or retransmission requests.
const MAX_RECEIVE_PER_TURN: usize = 256;

/// Lock-free state published by the audio thread to the network thread so the
/// network thread updates its active sender, packet padding length, and
/// retransmission tracker only for confirmed timelines and matching formats.
struct Confirmed {
    attached: AtomicBool,
    active: AtomicBool,
    timeline: AtomicU64,
    rate: AtomicU32,
    channels: AtomicU8,
}

impl Confirmed {
    fn new() -> Confirmed {
        Confirmed {
            attached: AtomicBool::new(false),
            active: AtomicBool::new(false),
            timeline: AtomicU64::new(0),
            rate: AtomicU32::new(0),
            channels: AtomicU8::new(0),
        }
    }
}

/// Candidate sender metadata cached while waiting for the audio thread to
/// confirm a newly observed timeline, including its own [`Asking`] tracker so
/// contiguous packets arriving before adoption do not trigger spurious
/// retransmission requests while genuinely missing frames are still tracked.
#[derive(Clone, Copy)]
struct PendingSender {
    timeline: u64,
    from: SocketAddr,
    length: usize,
    asking: Asking,
}

/// What the network thread hands to the audio thread.
pub enum Incoming {
    /// An audio packet with its pre-parsed header.
    Packet {
        /// The buffer it was received into.
        buffer: Box<[u8]>,
        /// The parsed header of the packet.
        header: Audio,
        /// The number of its bytes, from the start of the buffer.
        length: usize,
        /// The reading of the raw clock when it arrived.
        arrival: i64,
    },
    /// The sender's answer to a report.
    Answer(Echo),
    /// A report left.
    Departed {
        /// Its sequence number.
        sequence: u64,
        /// The reading of the raw clock when it left.
        time: i64,
    },
}

/// A report and the needs it carries, made on the audio thread for the
/// network thread to send.
#[derive(Clone, Copy, Debug)]
pub struct Outgoing {
    /// The report.
    pub report: Report,
    /// The largest needs of the last stretches of the timeline it reports on.
    pub needs: Recent,
}

/// The sizes of what passes between the two threads.
#[derive(Clone, Copy, Debug)]
pub struct Sizes {
    /// The number of buffers for audio packets. They are the most audio
    /// packets that can wait for the audio thread at once.
    pub buffers: usize,
    /// The largest datagram that is received, in bytes.
    pub datagram: usize,
    /// The most answers, departures and reports that can wait at once.
    pub messages: usize,
}

/// The end of the network thread.
pub struct NetworkEnd {
    incoming: Producer<Incoming>,
    reports: Consumer<Outgoing>,
    spare: Consumer<Box<[u8]>>,
    /// A spare buffer taken and not handed over.
    kept: Option<Box<[u8]>>,
    confirmed: Arc<Confirmed>,
}

/// The end of the audio thread.
pub struct AudioEnd {
    incoming: Consumer<Incoming>,
    reports: Producer<Outgoing>,
    spare: Producer<Box<[u8]>>,
    confirmed: Arc<Confirmed>,
}

/// The two ends, with the buffers made and waiting at the network end.
#[must_use]
pub fn link(sizes: Sizes) -> (NetworkEnd, AudioEnd) {
    let (incoming_in, incoming_out) = ring(sizes.buffers + sizes.messages);
    let (reports_in, reports_out) = ring(sizes.messages);
    // Every buffer fits into the ring that hands them back, so the audio
    // thread can always hand a buffer back and never frees one.
    let (mut spare_in, spare_out) = ring(sizes.buffers);
    for _ in 0..sizes.buffers {
        // The ring has room for all of them.
        let _ = spare_in.put(vec![0u8; sizes.datagram].into_boxed_slice());
    }
    let confirmed = Arc::new(Confirmed::new());
    (
        NetworkEnd {
            incoming: incoming_in,
            reports: reports_out,
            spare: spare_out,
            kept: None,
            confirmed: Arc::clone(&confirmed),
        },
        AudioEnd {
            incoming: incoming_out,
            reports: reports_in,
            spare: spare_in,
            confirmed,
        },
    )
}

impl NetworkEnd {
    /// Hands the audio packet `bytes`, which arrived when the raw clock read
    /// `arrival`, to the audio thread, in one of the spare buffers. Says
    /// whether it was handed over: not when `bytes` is not a valid audio
    /// packet, when no buffer is spare, when it is longer than a buffer, or
    /// when the ring to the audio thread is full.
    ///
    /// [`ReceiverNetwork`] receives into the buffers and needs no copy; this
    /// is for a network end that gets its packets otherwise.
    pub fn hand_over(&mut self, bytes: &[u8], arrival: i64) -> bool {
        let Ok(header) = parse_audio(bytes) else {
            return false;
        };
        let Some(mut buffer) = self.kept.take().or_else(|| self.spare.take()) else {
            return false;
        };
        let Some(place) = buffer.get_mut(..bytes.len()) else {
            self.kept = Some(buffer);
            return false;
        };
        place.copy_from_slice(bytes);
        let item = Incoming::Packet {
            buffer,
            header,
            length: bytes.len(),
            arrival,
        };
        match self.incoming.put(item) {
            Ok(()) => true,
            Err(Incoming::Packet { buffer, .. }) => {
                self.kept = Some(buffer);
                false
            }
            Err(_) => false,
        }
    }
}

/// What the network thread of a receiver has done so far.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NetworkCounts {
    /// Audio packets handed to the audio thread.
    pub packets: u64,
    /// Answers to reports handed to the audio thread.
    pub answers: u64,
    /// Reports sent.
    pub reports: u64,
    /// Requests sent for frames to be sent again.
    pub requests: u64,
    /// Outgoing reports or requests dropped due to a transient send error.
    pub unsent: u64,
    /// Subset of `unsent` caused by per-destination policy (`EPERM`) or
    /// address availability (`EADDRNOTAVAIL`).
    pub blocked: u64,
    /// Datagrams dropped because the audio thread had not handed back a
    /// buffer, or had no room for another item.
    pub dropped: u64,
    /// Datagrams that were neither an audio packet of the stream nor an
    /// answer to this receiver's reports.
    pub other: u64,
}

/// The network thread of a receiver.
pub struct ReceiverNetwork {
    socket: Socket,
    end: NetworkEnd,
    stream: u16,
    /// Where datagrams go when there is no buffer, to be dropped.
    overflow: Box<[u8]>,
    /// Where reports are written.
    outgoing: Box<[u8]>,
    /// The sender of the confirmed timeline of the stream, to which reports
    /// and retransmission requests go.
    sender: Option<SocketAddr>,
    /// The confirmed timeline associated with `sender`.
    sender_timeline: Option<u64>,
    /// The length of packets on that timeline, to which reports are padded.
    length: usize,
    /// Sender metadata of the most recent unconfirmed timeline candidate.
    pending: Option<PendingSender>,
    /// The frames that are missing and asked for.
    asking: Asking,
    counts: NetworkCounts,
}

impl ReceiverNetwork {
    /// The network thread of a receiver of `stream` that receives on
    /// `socket`, at the network end of a link of `sizes`.
    #[must_use]
    pub fn new(socket: Socket, end: NetworkEnd, stream: u16, sizes: Sizes) -> ReceiverNetwork {
        ReceiverNetwork {
            socket,
            end,
            stream,
            overflow: vec![0u8; sizes.datagram].into_boxed_slice(),
            outgoing: vec![0u8; sizes.datagram.max(packet::REPORT + packet::NEEDS)]
                .into_boxed_slice(),
            sender: None,
            sender_timeline: None,
            length: 0,
            pending: None,
            asking: Asking::new(),
            counts: NetworkCounts::default(),
        }
    }

    /// What it has done so far.
    #[must_use]
    pub fn counts(&self) -> NetworkCounts {
        self.counts
    }

    /// The socket.
    #[must_use]
    pub fn socket(&self) -> &Socket {
        &self.socket
    }

    /// Promotes any cached candidate sender once the audio thread confirms its
    /// timeline.
    fn sync_confirmed(&mut self) {
        if !self.end.confirmed.active.load(Ordering::Acquire) {
            return;
        }
        let timeline = self.end.confirmed.timeline.load(Ordering::Acquire);
        if self.sender_timeline == Some(timeline) {
            return;
        }
        if let Some(pending) = self.pending
            && pending.timeline == timeline
        {
            self.sender = Some(pending.from);
            self.sender_timeline = Some(timeline);
            self.length = pending.length;
            self.asking = pending.asking;
            self.pending = None;
        }
    }

    /// Computes how long `socket.wait` should sleep, returning early if
    /// outgoing reports are queued or an active retransmission request is due
    /// sooner than `milliseconds`.
    fn wait_timeout(&self, milliseconds: i32) -> i32 {
        if self.end.reports.waiting() > 0 {
            return 0;
        }
        if self.sender.is_some()
            && let Some(due_ns) = self.asking.next_due(clock::raw())
        {
            let due_ms = i32::try_from(due_ns.saturating_add(999_999).max(0) / 1_000_000)
                .unwrap_or(i32::MAX);
            return if milliseconds < 0 {
                due_ms
            } else {
                milliseconds.min(due_ms)
            };
        }
        milliseconds
    }

    /// Waits up to `milliseconds` for something to do (or less when reports or
    /// retransmission requests are due), and does all there is: takes in the
    /// datagrams that arrived, hands over the departures of reports, and sends
    /// the reports that the audio thread made.
    ///
    /// # Errors
    ///
    /// A fatal error of the socket.
    pub fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        self.sync_confirmed();
        let wait_ms = self.wait_timeout(milliseconds);
        self.socket.wait(wait_ms)?;
        for _ in 0..MAX_RECEIVE_PER_TURN {
            if !self.receive()? {
                break;
            }
        }
        while let Some(departure) = self.socket.departure()? {
            let departed = Incoming::Departed {
                sequence: departure.tag,
                time: departure.stamp.time,
            };
            if self.end.incoming.put(departed).is_err() {
                self.counts.dropped += 1;
            }
        }
        self.sync_confirmed();
        while let Some(outgoing) = self.end.reports.take() {
            self.send(&outgoing)?;
        }
        self.ask()
    }

    /// Asks the sender for the frames that are missing and due to be asked
    /// for.
    fn ask(&mut self) -> io::Result<()> {
        let Some(to) = self.sender else {
            return Ok(());
        };
        let now = clock::raw();
        while let Some(wanted) = self.asking.due(now) {
            let request = Request {
                stream: self.stream,
                timeline: wanted.timeline,
                first: wanted.first,
                frames: wanted.frames,
            };
            let Some(length) = write_request(&request, &mut self.outgoing) else {
                break;
            };
            let bytes = self.outgoing.get(..length).unwrap_or(&[]);
            match self.socket.send_untagged(bytes, to) {
                Ok(_) => self.counts.requests += 1,
                // It is asked again in ten milliseconds.
                Err(error) if is_transient_send_error(&error) => {
                    self.record_unsent(&error);
                    break;
                }
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }

    /// Updates `sender`, `length`, and `asking` for an accepted audio packet,
    /// gating state changes on audio-thread confirmation when an audio end is
    /// attached so single stray packets cannot hijack reports or wipe missing
    /// runs.
    fn record_audio(&mut self, header: &Audio, from: SocketAddr, length: usize, arrival: i64) {
        self.sync_confirmed();
        if !self.end.confirmed.attached.load(Ordering::Acquire) {
            self.sender = Some(from);
            self.sender_timeline = Some(header.timeline);
            self.length = length;
            self.asking.arrived(header, arrival);
            return;
        }
        let active = self.end.confirmed.active.load(Ordering::Acquire);
        let confirmed = self.end.confirmed.timeline.load(Ordering::Acquire);
        if active && header.timeline == confirmed {
            if self.sender_timeline != Some(confirmed) {
                self.sender = Some(from);
                self.sender_timeline = Some(confirmed);
                self.length = length;
                self.asking.arrived(header, arrival);
            } else if self
                .sender
                .is_some_and(|known| canonical_addr(known) == canonical_addr(from))
            {
                self.length = length;
                self.asking.arrived(header, arrival);
            }
        } else {
            // Unconfirmed timeline: track arriving packets in `pending.asking`
            // without disturbing the active sender or retransmission tracker.
            match &mut self.pending {
                Some(pending) if pending.timeline == header.timeline => {
                    if canonical_addr(pending.from) == canonical_addr(from) {
                        pending.length = length;
                        pending.asking.arrived(header, arrival);
                    }
                }
                _ => {
                    let mut asking = Asking::new();
                    asking.arrived(header, arrival);
                    self.pending = Some(PendingSender {
                        timeline: header.timeline,
                        from,
                        length,
                        asking,
                    });
                }
            }
        }
    }

    /// Takes in one datagram, if one is waiting, and says whether one was.
    fn receive(&mut self) -> io::Result<bool> {
        if self.end.kept.is_none() {
            self.end.kept = self.end.spare.take();
        }
        let Some(buffer) = self.end.kept.as_mut() else {
            // No buffer to hand over: the datagram is read and dropped.
            return Ok(match self.socket.receive(&mut self.overflow)? {
                Some(_) => {
                    self.counts.dropped += 1;
                    true
                }
                None => false,
            });
        };
        let Some(received) = self.socket.receive(buffer)? else {
            return Ok(false);
        };
        let bytes = buffer.get(..received.length).unwrap_or(&[]);
        match packet::kind(bytes) {
            Ok(KIND_AUDIO) => match parse_audio(bytes) {
                Ok(header) if header.stream == self.stream => {
                    let expected_rate = self.end.confirmed.rate.load(Ordering::Acquire);
                    let expected_channels = self.end.confirmed.channels.load(Ordering::Acquire);
                    if (expected_rate != 0 && header.rate != expected_rate)
                        || (expected_channels != 0 && header.channels != expected_channels)
                    {
                        self.counts.other += 1;
                        return Ok(true);
                    }
                    self.record_audio(
                        &header,
                        received.from,
                        received.length,
                        received.arrival.time,
                    );
                    if let Some(buffer) = self.end.kept.take() {
                        let item = Incoming::Packet {
                            buffer,
                            header,
                            length: received.length,
                            arrival: received.arrival.time,
                        };
                        match self.end.incoming.put(item) {
                            Ok(()) => self.counts.packets += 1,
                            Err(Incoming::Packet { buffer, .. }) => {
                                // The buffer is kept for the next datagram.
                                self.end.kept = Some(buffer);
                                self.counts.dropped += 1;
                            }
                            Err(_) => self.counts.dropped += 1,
                        }
                    }
                }
                _ => self.counts.other += 1,
            },
            Ok(KIND_ECHO) => match parse_echo(bytes) {
                Ok(echo) if echo.stream == self.stream => {
                    self.sync_confirmed();
                    if self
                        .sender
                        .is_some_and(|known| canonical_addr(known) != canonical_addr(received.from))
                    {
                        self.counts.other += 1;
                    } else if self.end.incoming.put(Incoming::Answer(echo)).is_err() {
                        self.counts.dropped += 1;
                    } else {
                        self.counts.answers += 1;
                    }
                }
                _ => self.counts.other += 1,
            },
            _ => self.counts.other += 1,
        }
        Ok(true)
    }

    /// Sends a report and its needs to the sender of the stream, padded to at
    /// least the space required for needs and the length of the stream's audio
    /// packets. A report made before any audio packet arrived has nowhere to
    /// go and is dropped.
    fn send(&mut self, outgoing: &Outgoing) -> io::Result<()> {
        let report = &outgoing.report;
        let Some(to) = self.sender else {
            return Ok(());
        };
        let min_len = packet::REPORT + packet::NEEDS;
        let target_len = self.length.clamp(min_len, self.outgoing.len());
        let Some(length) = write_report(report, &mut self.outgoing, target_len) else {
            return Ok(());
        };
        if let Some(padded) = self.outgoing.get_mut(..length) {
            write_needs(&outgoing.needs, padded);
        }
        let bytes = self.outgoing.get(..length).unwrap_or(&[]);
        match self.socket.send_to(bytes, to, report.sequence) {
            Ok(_) => {
                self.counts.reports += 1;
                Ok(())
            }
            // A report that cannot be sent now is not sent again: the next
            // one serves as well.
            Err(error) if is_transient_send_error(&error) => {
                self.record_unsent(&error);
                Ok(())
            }
            Err(error) => Err(error),
        }
    }

    /// Counts a transient send error, breaking out per-destination policy or
    /// address-availability failures (`EPERM`, `EADDRNOTAVAIL`) into `blocked`.
    fn record_unsent(&mut self, error: &io::Error) {
        self.counts.unsent += 1;
        if is_restricted_send_error(error) {
            self.counts.blocked += 1;
        }
    }
}

impl NetworkLoop for ReceiverNetwork {
    fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        ReceiverNetwork::turn(self, milliseconds)
    }
}

/// When a receiver sends reports. The delay of a path is a constant that the
/// receiver remembers for about a minute, so reports are sent often only at
/// the start, to find it soon, and rarely after.
#[derive(Clone, Copy, Debug)]
pub struct Reporting {
    /// The time between two reports at the start, in nanoseconds.
    pub at_start: i64,
    /// How long the start lasts, from the first report, in nanoseconds.
    pub start: i64,
    /// The time between two reports after the start, in nanoseconds.
    pub after: i64,
}

impl Reporting {
    /// Twenty reports a second for five seconds, then five a second. In
    /// simulation five a second measure the path within a few microseconds of
    /// what twenty do, on wired and wireless links alike; one a second is
    /// four times worse.
    pub const USUAL: Reporting = Reporting {
        at_start: 50_000_000,
        start: 5_000_000_000,
        after: 200_000_000,
    };
}

/// What the audio thread of a receiver is set up with.
#[derive(Clone, Copy, Debug)]
pub struct Intake {
    /// The most items taken in at the start of a cycle.
    pub items: usize,
    /// When reports are sent; `None` for a receiver that sends none.
    pub reports: Option<Reporting>,
}

/// A receiver's playback with the end of the audio thread: what a playback
/// device plays.
pub struct ReceiverAudio<const N: usize, const M: usize, const K: usize, const W: usize> {
    playback: ReceiverPlayback<N, M, K, W>,
    end: AudioEnd,
    intake: Intake,
    /// When the first report was made and when the next is due, on the raw
    /// clock; `None` before the first report.
    reported: Option<(i64, i64)>,
    /// Reports that found no room in the ring.
    unsent: u64,
}

impl<const N: usize, const M: usize, const K: usize, const W: usize> ReceiverAudio<N, M, K, W> {
    /// The audio thread of a receiver that plays `playback`, at the audio
    /// end of a link.
    #[must_use]
    pub fn new(playback: ReceiverPlayback<N, M, K, W>, end: AudioEnd, intake: Intake) -> Self {
        end.confirmed.rate.store(playback.rate(), Ordering::Release);
        end.confirmed
            .channels
            .store(playback.channels_u8(), Ordering::Release);
        end.confirmed.attached.store(true, Ordering::Release);
        ReceiverAudio {
            playback,
            end,
            intake,
            reported: None,
            unsent: 0,
        }
    }

    /// The receiver's playback.
    #[must_use]
    pub fn playback(&self) -> &ReceiverPlayback<N, M, K, W> {
        &self.playback
    }

    /// Reports that found no room in the ring to the network thread.
    #[must_use]
    pub fn unsent(&self) -> u64 {
        self.unsent
    }

    /// Takes in what the network thread handed over, up to the set number
    /// of items.
    fn take_in(&mut self) {
        for _ in 0..self.intake.items {
            let Some(item) = self.end.incoming.take() else {
                return;
            };
            match item {
                Incoming::Packet {
                    buffer,
                    header,
                    length,
                    arrival,
                } => {
                    if let Some(bytes) = buffer.get(..length)
                        && let Some(payload) = bytes.get(packet::HEADER..)
                        && let Some(heard) = self.playback.packet(&header, payload, arrival)
                        && !heard.ignored
                    {
                        self.end
                            .confirmed
                            .timeline
                            .store(header.timeline, Ordering::Release);
                        self.end.confirmed.active.store(true, Ordering::Release);
                    }
                    // The ring holds every buffer there is, so it has room
                    // for this one. Were it full, the buffer would be kept
                    // rather than freed: freeing memory is not done on this
                    // thread.
                    if let Err(buffer) = self.end.spare.put(buffer) {
                        std::mem::forget(buffer);
                    }
                }
                Incoming::Answer(echo) => self.playback.echo(&echo),
                Incoming::Departed { sequence, time } => self.playback.reported(sequence, time),
            }
        }
    }

    /// Makes a report when one is due at `time`. Resets the schedule if device
    /// timestamps jump backwards or place `due` impossibly far ahead so
    /// reporting never stalls.
    fn report(&mut self, time: i64) {
        let Some(reporting) = self.intake.reports else {
            return;
        };
        let at_start = reporting.at_start.max(0);
        let after = reporting.after.max(0);
        let max_period = at_start.max(after);
        if let Some((first, due)) = self.reported {
            let jumped = time < first || due.saturating_sub(time) > max_period;
            if jumped {
                self.reported = None;
            } else if time < due {
                return;
            }
        }
        let Some(report) = self.playback.report() else {
            return;
        };
        let outgoing = Outgoing {
            report,
            needs: self.playback.recent(),
        };
        let first = self.reported.map_or(time, |(first, _)| first);
        let period = if time.saturating_sub(first) < reporting.start.max(0) {
            at_start
        } else {
            after
        };
        self.reported = Some((first, time.saturating_add(period)));
        if self.end.reports.put(outgoing).is_err() {
            self.unsent += 1;
        }
    }
}

impl<const N: usize, const M: usize, const K: usize, const W: usize> Playback
    for ReceiverAudio<N, M, K, W>
{
    fn channels(&self) -> usize {
        self.playback.channels()
    }

    fn cycle(&mut self, frames: &mut [f32], position: u64, time: i64) {
        self.take_in();
        self.playback.cycle(frames, position, time);
        self.report(time);
    }
}

#[cfg(test)]
mod tests {
    use std::net::{SocketAddr, UdpSocket};
    use std::time::Duration;

    use unisono_core::packet::{
        self, Audio, Format, PROTECTION_ON_REQUEST, Recent, Report, parse_needs, parse_report,
        write_audio,
    };
    use unisono_core::player::Regulation;
    use unisono_dsp::Parameters;

    use super::{Intake, Outgoing, ReceiverAudio, ReceiverNetwork, Reporting, Sizes, link};
    use crate::audio::Playback;
    use crate::pump::{ReceiverPlayback, Settings};
    use crate::socket::Socket;

    fn playback_settings() -> Settings {
        Settings {
            stream: 3,
            rate: 48_000,
            channels: 2,
            identity: 1,
            silence: 1_000_000_000,
            slope_limit: 200_000,
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
            concealment: Parameters::for_rate(48_000),
            block: 256,
            device_range: 10_000_000,
        }
    }

    fn audio_packet(stream: u16, timeline: u64, index: u64, rate: u32, frames: u16) -> Vec<u8> {
        let header = Audio {
            stream,
            timeline,
            index,
            capture: 0,
            rate,
            frames,
            channels: 2,
            format: Format::Signed24,
            level: 30_000_000,
            level_slope: 0,
            span: 2_000,
            window: 2_400,
            flags: 0,
            protection: PROTECTION_ON_REQUEST,
            stamped_index: 0,
            stamped_departure: 0,
            drift: 0,
            clock: 1,
        };
        let payload = usize::from(frames) * 2 * 3;
        let mut buf = vec![0u8; packet::HEADER + payload];
        let len = write_audio(&header, &mut buf).expect("write audio");
        buf.truncate(len);
        buf
    }

    #[test]
    fn stray_timeline_and_wrong_format_packets_do_not_hijack_sender_or_asking() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let rx_sock = Socket::bind(loopback).expect("rx");
        let rx_addr = rx_sock.address().expect("rx addr");
        let legit = UdpSocket::bind(loopback).expect("legit");
        let legit_addr = legit.local_addr().expect("legit addr");
        let stray = UdpSocket::bind(loopback).expect("stray");

        let sizes = Sizes {
            buffers: 16,
            datagram: 2_048,
            messages: 16,
        };
        let (net_end, audio_end) = link(sizes);
        let mut net = ReceiverNetwork::new(rx_sock, net_end, 3, sizes);
        let playback: ReceiverPlayback<16, 16, 4, 64> = ReceiverPlayback::new(&playback_settings());
        let mut audio = ReceiverAudio::new(
            playback,
            audio_end,
            Intake {
                items: 16,
                reports: Some(Reporting::USUAL),
            },
        );

        // Legitimate packet 0 -> audio thread confirms timeline 10.
        legit
            .send_to(&audio_packet(3, 10, 0, 48_000, 240), rx_addr)
            .expect("send 0");
        net.turn(0).expect("turn 1");
        let mut out = [0.0f32; 512];
        audio.cycle(&mut out, 0, 1_000_000);
        net.turn(0).expect("turn 2");
        assert_eq!(net.sender, Some(legit_addr));
        assert_eq!(net.sender_timeline, Some(10));

        // Packet with wrong sample rate is rejected at network ingress.
        let before_other = net.counts().other;
        stray
            .send_to(&audio_packet(3, 10, 240, 44_100, 240), rx_addr)
            .expect("send bad rate");
        net.turn(0).expect("turn 3");
        assert_eq!(net.counts().other, before_other + 1);
        assert_eq!(net.sender, Some(legit_addr));

        // Single stray packet with a different timeline must NOT hijack `sender`.
        stray
            .send_to(&audio_packet(3, 99, 0, 48_000, 240), rx_addr)
            .expect("send stray");
        net.turn(0).expect("turn 4");
        audio.cycle(&mut out, 256, 6_333_333);
        net.turn(0).expect("turn 5");
        assert_eq!(net.sender, Some(legit_addr));
        assert_eq!(net.sender_timeline, Some(10));
    }

    #[test]
    fn short_audio_packet_still_leaves_room_for_needs_in_reports() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let rx_sock = Socket::bind(loopback).expect("rx");
        let sender = UdpSocket::bind(loopback).expect("sender");
        sender
            .set_read_timeout(Some(Duration::from_secs(1)))
            .expect("timeout");
        let sizes = Sizes {
            buffers: 8,
            datagram: 2_048,
            messages: 8,
        };
        let (net_end, _audio_end) = link(sizes);
        let mut net = ReceiverNetwork::new(rx_sock, net_end, 3, sizes);
        net.sender = Some(sender.local_addr().expect("addr"));
        // Even if `length` were artificially tiny (below REPORT + NEEDS),
        // `send()` pads to at least `REPORT + NEEDS` so needs are never dropped.
        net.length = 32;
        let mut recent = Recent::NONE;
        recent.count = 2;
        recent.newest = 5;
        recent.needs[0] = 12_345;
        recent.needs[1] = 23_456;
        let outgoing = Outgoing {
            report: Report {
                stream: 3,
                timeline: 10,
                receiver: 1,
                sequence: 7,
            },
            needs: recent,
        };
        net.send(&outgoing).expect("send report");
        let mut buf = [0u8; 256];
        let (len, _) = sender.recv_from(&mut buf).expect("recv report");
        assert!(len >= packet::REPORT + packet::NEEDS);
        assert_eq!(parse_report(&buf[..len]), Ok(outgoing.report));
        let parsed_needs = parse_needs(&buf[..len]);
        assert_eq!(parsed_needs.count, 2);
        assert_eq!(parsed_needs.newest, 5);
        assert_eq!(parsed_needs.needs[0], 12_345);
        assert_eq!(parsed_needs.needs[1], 23_456);
    }

    #[test]
    fn report_schedule_recovers_from_device_timestamp_jumps() {
        let sizes = Sizes {
            buffers: 8,
            datagram: 2_048,
            messages: 8,
        };
        let (mut net_end, audio_end) = link(sizes);
        let playback: ReceiverPlayback<16, 16, 4, 64> = ReceiverPlayback::new(&playback_settings());
        let mut audio = ReceiverAudio::new(
            playback,
            audio_end,
            Intake {
                items: 8,
                reports: Some(Reporting::USUAL),
            },
        );
        // Adopt a timeline so `playback.report()` returns `Some`.
        assert!(net_end.hand_over(&audio_packet(3, 10, 0, 48_000, 240), 1_000_000));
        let mut out = [0.0f32; 512];
        // Normal report at t = 1_000_000_000.
        audio.cycle(&mut out, 0, 1_000_000_000);
        assert!(net_end.reports.take().is_some());
        // Wild forward glitch sets `due` to 10_000_050_000_000.
        audio.cycle(&mut out, 256, 10_000_000_000_000);
        assert!(net_end.reports.take().is_some());
        // Returning to normal time t = 1_010_000_000 must recover immediately
        // instead of stalling until t = 10_000_050_000_000!
        audio.cycle(&mut out, 512, 1_010_000_000);
        assert!(net_end.reports.take().is_some());
    }

    #[test]
    fn lossless_contiguous_packets_draw_no_request_at_adoption() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let rx_sock = Socket::bind(loopback).expect("rx");
        let rx_addr = rx_sock.address().expect("rx addr");
        let tx = UdpSocket::bind(loopback).expect("tx");
        tx.set_read_timeout(Some(Duration::from_millis(50)))
            .expect("timeout");

        let sizes = Sizes {
            buffers: 32,
            datagram: 2_048,
            messages: 32,
        };
        let (net_end, audio_end) = link(sizes);
        let mut net = ReceiverNetwork::new(rx_sock, net_end, 3, sizes);
        let playback: ReceiverPlayback<64, 64, 8, 64> = ReceiverPlayback::new(&playback_settings());
        let mut audio = ReceiverAudio::new(
            playback,
            audio_end,
            Intake {
                items: 16,
                reports: None,
            },
        );

        // Packets 0 and 240 arrive before the audio thread runs its first cycle.
        tx.send_to(&audio_packet(3, 7, 0, 48_000, 240), rx_addr)
            .expect("send 0");
        tx.send_to(&audio_packet(3, 7, 240, 48_000, 240), rx_addr)
            .expect("send 240");
        std::thread::sleep(Duration::from_millis(10));
        net.turn(0).expect("turn 1");
        let mut out = [0.0f32; 512];
        audio.cycle(&mut out, 0, 10_000_000);
        // Packet 480 follows contiguously after adoption: nothing is missing.
        tx.send_to(&audio_packet(3, 7, 480, 48_000, 240), rx_addr)
            .expect("send 480");
        std::thread::sleep(Duration::from_millis(10));
        net.turn(0).expect("turn 2");
        assert_eq!(net.counts().requests, 0);

        // Now switch to timeline 8 with a real gap (0 and 480 arrive before
        // adoption, 240 is missing): confirming timeline 8 must request 240..480.
        tx.send_to(&audio_packet(3, 8, 0, 48_000, 240), rx_addr)
            .expect("send t8 0");
        tx.send_to(&audio_packet(3, 8, 480, 48_000, 240), rx_addr)
            .expect("send t8 480");
        std::thread::sleep(Duration::from_millis(10));
        net.turn(0).expect("turn 3");
        // No request sent for unconfirmed timeline 8 yet.
        assert_eq!(net.counts().requests, 0);
        audio.cycle(&mut out, 256, 15_333_333);
        net.turn(0).expect("turn 4");
        assert_eq!(net.counts().requests, 1);
    }
}
