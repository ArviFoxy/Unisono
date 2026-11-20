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

use unisono_core::packet::{
    self, Echo, KIND_AUDIO, KIND_ECHO, Report, parse_audio, parse_echo, write_report,
};

use crate::audio::Playback;
use crate::pump::ReceiverPlayback;
use crate::ring::{Consumer, Producer, ring};
use crate::socket::Socket;

/// What the network thread hands to the audio thread.
pub enum Incoming {
    /// An audio packet.
    Packet {
        /// The buffer it was received into.
        buffer: Box<[u8]>,
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
    reports: Consumer<Report>,
    spare: Consumer<Box<[u8]>>,
    /// A spare buffer taken and not handed over.
    kept: Option<Box<[u8]>>,
}

/// The end of the audio thread.
pub struct AudioEnd {
    incoming: Consumer<Incoming>,
    reports: Producer<Report>,
    spare: Producer<Box<[u8]>>,
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
    (
        NetworkEnd {
            incoming: incoming_in,
            reports: reports_out,
            spare: spare_out,
            kept: None,
        },
        AudioEnd {
            incoming: incoming_out,
            reports: reports_in,
            spare: spare_in,
        },
    )
}

impl NetworkEnd {
    /// Hands the audio packet `bytes`, which arrived when the raw clock read
    /// `arrival`, to the audio thread, in one of the spare buffers. Says
    /// whether it was handed over: not when no buffer is spare, when it is
    /// longer than a buffer, or when the ring to the audio thread is full.
    ///
    /// [`ReceiverNetwork`] receives into the buffers and needs no copy; this
    /// is for a network end that gets its packets otherwise.
    pub fn hand_over(&mut self, bytes: &[u8], arrival: i64) -> bool {
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
    /// The sender of the last audio packet of the stream, to which reports
    /// go.
    sender: Option<SocketAddr>,
    /// The length of that packet, to which reports are padded.
    length: usize,
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
            outgoing: vec![0u8; sizes.datagram.max(packet::REPORT)].into_boxed_slice(),
            sender: None,
            length: 0,
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

    /// Waits up to `milliseconds` for something to do, and does all there
    /// is: takes in the datagrams that arrived, hands over the departures of
    /// reports, and sends the reports that the audio thread made.
    ///
    /// # Errors
    ///
    /// An error of the socket other than that nothing is waiting.
    pub fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        self.socket.wait(milliseconds)?;
        while self.receive()? {}
        while let Some(departure) = self.socket.departure()? {
            let departed = Incoming::Departed {
                sequence: departure.tag,
                time: departure.stamp.time,
            };
            if self.end.incoming.put(departed).is_err() {
                self.counts.dropped += 1;
            }
        }
        while let Some(report) = self.end.reports.take() {
            self.send(&report)?;
        }
        Ok(())
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
                    self.sender = Some(received.from);
                    self.length = received.length;
                    if let Some(buffer) = self.end.kept.take() {
                        let item = Incoming::Packet {
                            buffer,
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
                    if self.end.incoming.put(Incoming::Answer(echo)).is_err() {
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

    /// Sends a report to the sender of the stream, padded to the length of
    /// its audio packets. A report made before any audio packet arrived has
    /// nowhere to go and is dropped.
    fn send(&mut self, report: &Report) -> io::Result<()> {
        let Some(to) = self.sender else {
            return Ok(());
        };
        let Some(length) = write_report(report, &mut self.outgoing, self.length) else {
            return Ok(());
        };
        let bytes = self.outgoing.get(..length).unwrap_or(&[]);
        match self.socket.send_to(bytes, to, report.sequence) {
            Ok(_) => {
                self.counts.reports += 1;
                Ok(())
            }
            // A report that cannot be sent now is not sent again: the next
            // one serves as well.
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => Ok(()),
            Err(error) => Err(error),
        }
    }
}

/// What the audio thread of a receiver is set up with.
#[derive(Clone, Copy, Debug)]
pub struct Intake {
    /// The most items taken in at the start of a cycle.
    pub items: usize,
    /// The time between two reports, in nanoseconds; `None` for a receiver
    /// that sends no reports, as one that is told the delay of its path.
    pub report_period: Option<i64>,
}

/// A receiver's playback with the end of the audio thread: what a playback
/// device plays.
pub struct ReceiverAudio<const N: usize, const M: usize, const K: usize, const W: usize> {
    playback: ReceiverPlayback<N, M, K, W>,
    end: AudioEnd,
    intake: Intake,
    /// When the next report is made, on the raw clock; `None` before the
    /// first cycle.
    next_report: Option<i64>,
    /// Reports that found no room in the ring.
    unsent: u64,
}

impl<const N: usize, const M: usize, const K: usize, const W: usize> ReceiverAudio<N, M, K, W> {
    /// The audio thread of a receiver that plays `playback`, at the audio
    /// end of a link.
    #[must_use]
    pub fn new(playback: ReceiverPlayback<N, M, K, W>, end: AudioEnd, intake: Intake) -> Self {
        ReceiverAudio {
            playback,
            end,
            intake,
            next_report: None,
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
                    length,
                    arrival,
                } => {
                    if let Some(bytes) = buffer.get(..length)
                        && let Ok(header) = parse_audio(bytes)
                        && let Some(payload) = bytes.get(packet::HEADER..)
                    {
                        self.playback.packet(&header, payload, arrival);
                    }
                    // The ring holds every buffer there is, so it has room
                    // for this one, and the buffer is not freed here.
                    let _ = self.end.spare.put(buffer);
                }
                Incoming::Answer(echo) => self.playback.echo(&echo),
                Incoming::Departed { sequence, time } => self.playback.reported(sequence, time),
            }
        }
    }

    /// Makes a report when one is due at `time`.
    fn report(&mut self, time: i64) {
        let Some(period) = self.intake.report_period else {
            return;
        };
        let due = *self.next_report.get_or_insert(time);
        if time < due {
            return;
        }
        self.next_report = Some(time.saturating_add(period));
        if let Some(report) = self.playback.report()
            && self.end.reports.put(report).is_err()
        {
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
