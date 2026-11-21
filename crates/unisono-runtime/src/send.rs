// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The two threads of a sender, and what passes between them.
//!
//! The **capture thread** is the audio system's: once in each cycle of the
//! capture device it hands over the frames of the cycle with the device's
//! count of the first frame and the time the device reports for it, and
//! nothing else. The **network thread** owns everything else: the core's
//! sender, the line through the capture device's reports, and the socket. It
//! cuts the frames into packets, stamps each with the capture time of its
//! first frame, sends it to every receiver, takes in when packets left, and
//! answers reports. From the needs that the reports carry it chooses the
//! level, if it is set up to (see [`crate::level`]), and moves the level
//! there at a set slope.
//!
//! The frames cross in buffers that are made once and go round, as in
//! [`crate::receive`]. When the network thread does not hand buffers back,
//! the capture thread has none to fill, drops the cycle and counts it.
//!
//! # The index and the device's count
//!
//! A timeline's index counts the frames of the capture device from where the
//! timeline began, so the index of a frame is its count minus the count at
//! that start. When the capture thread drops cycles, the frames of those
//! cycles are sent as silence, so that the index stays the device's count and
//! the receivers go on. When the count goes back, or jumps further than
//! [`LONGEST_GAP`] frames ahead, the device started anew, and so does the
//! timeline.

use std::io;
use std::net::SocketAddr;

use unisono_core::device::Device;
use unisono_core::packet::{
    self, Audio, Format, KIND_REPORT, parse_needs, parse_report, write_audio, write_echo,
};
use unisono_core::sender::{Sender, Settings as SenderSettings};
use unisono_dsp::format::{to_signed16, to_signed24};

use crate::audio::Capture;
use crate::level::{Checks, Choice, Chooser};
use crate::ring::{Consumer, Producer, ring};
use crate::socket::Socket;

/// The most frames that are sent as silence in place of dropped cycles. A
/// longer gap starts a timeline anew: 2^20 frames, about 22 seconds at
/// 48,000 frames a second.
pub const LONGEST_GAP: u64 = 1_048_576;

/// The cycle of a capture device, in a buffer that goes round.
pub struct Captured {
    /// The buffer, whose first `frames` frames are the cycle's.
    pub buffer: Box<[f32]>,
    /// The number of frames.
    pub frames: usize,
    /// The device's count of the first frame.
    pub position: u64,
    /// The time the device reports for the first frame, on the raw clock.
    pub time: i64,
}

/// The end of the capture thread: what a capture device hands its frames to.
pub struct CaptureEnd {
    channels: usize,
    full: Producer<Captured>,
    spare: Consumer<Box<[f32]>>,
    dropped: u64,
}

/// The end of the network thread.
pub struct SenderEnd {
    full: Consumer<Captured>,
    spare: Producer<Box<[f32]>>,
}

/// The two ends, with `buffers` buffers of `frames` frames of `channels`
/// samples made and waiting at the capture end.
#[must_use]
pub fn link(buffers: usize, frames: usize, channels: usize) -> (CaptureEnd, SenderEnd) {
    let (full_in, full_out) = ring(buffers);
    // Every buffer fits into the ring that hands them back.
    let (mut spare_in, spare_out) = ring(buffers);
    for _ in 0..buffers {
        // The ring has room for all of them.
        let _ = spare_in.put(vec![0.0f32; frames.saturating_mul(channels)].into_boxed_slice());
    }
    (
        CaptureEnd {
            channels,
            full: full_in,
            spare: spare_out,
            dropped: 0,
        },
        SenderEnd {
            full: full_out,
            spare: spare_in,
        },
    )
}

impl CaptureEnd {
    /// The cycles dropped because no buffer was spare, or the cycle was
    /// larger than a buffer.
    #[must_use]
    pub fn dropped(&self) -> u64 {
        self.dropped
    }
}

impl Capture for CaptureEnd {
    fn channels(&self) -> usize {
        self.channels
    }

    fn cycle(&mut self, frames: &[f32], position: u64, time: i64) {
        let Some(mut buffer) = self.spare.take() else {
            self.dropped += 1;
            return;
        };
        let Some(place) = buffer.get_mut(..frames.len()) else {
            self.dropped += 1;
            // The buffer is too small; it goes on as an empty cycle, so that
            // it comes back.
            let empty = Captured {
                buffer,
                frames: 0,
                position,
                time,
            };
            keep(self.full.put(empty));
            return;
        };
        place.copy_from_slice(frames);
        let count = frames.len() / self.channels.max(1);
        let item = Captured {
            buffer,
            frames: count,
            position,
            time,
        };
        // The ring holds every buffer there is, so it has room for this one.
        if let Err(item) = self.full.put(item) {
            self.dropped += 1;
            keep(Err(item));
        }
    }
}

/// Keeps the buffer of an item that a full ring gave back, rather than
/// freeing it: freeing memory is not done on the capture thread. The rings
/// hold every buffer there is, so this does not happen.
fn keep(result: Result<(), Captured>) {
    if let Err(item) = result {
        std::mem::forget(item.buffer);
    }
}

/// What a sender is set up with.
#[derive(Clone, Debug)]
pub struct Settings {
    /// What stays the same in every packet of the stream; its `clock` is the
    /// identity of the sender's clock (see [`clock_identity`]).
    pub stream: SenderSettings,
    /// The number of frames in a packet.
    pub packet: u16,
    /// The latency that every receiver holds at the start, in nanoseconds.
    pub level: i64,
    /// How the level is chosen from the needs that receivers report;
    /// `None` holds it where it starts.
    pub choice: Option<Choice>,
    /// The number of the first timeline (see [`first_timeline`]).
    pub timeline: u64,
    /// Where the packets go.
    pub receivers: Vec<SocketAddr>,
}

/// What the network thread of a sender has done so far.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SenderCounts {
    /// Audio packets made; each is sent to every receiver.
    pub packets: u64,
    /// Frames sent as silence for cycles that the capture thread dropped.
    pub filled: u64,
    /// Timelines started after the first.
    pub restarts: u64,
    /// Reports answered.
    pub answers: u64,
    /// Datagrams that could not be sent.
    pub unsent: u64,
    /// Moves of the level that were begun.
    pub moves: u64,
}

/// The network thread of a sender.
pub struct SenderNetwork {
    socket: Socket,
    end: SenderEnd,
    sender: Sender,
    /// The line through the capture device's reports.
    device: Device<64>,
    settings: Settings,
    /// The device's count at the start of the timeline.
    origin: Option<u64>,
    /// Frames captured and not yet sent, interleaved, from the frame with
    /// index `sender.next()` on.
    waiting: Vec<f32>,
    /// Where a packet is written.
    bytes: Box<[u8]>,
    /// Where datagrams are received.
    incoming: Box<[u8]>,
    /// What chooses the level, if it is chosen.
    chooser: Option<Chooser>,
    /// The level that the level moves to, while it moves.
    target: Option<i64>,
    /// The index of the next frame when the level was last chosen.
    chosen: u64,
    counts: SenderCounts,
}

/// The bits of a departure's tag that hold the index; the bits above hold
/// the low bits of the timeline's number, so that a departure of a timeline
/// before is told apart.
const INDEX_BITS: u32 = 48;

/// The tag of the departures of answers, which are not taken in.
const ANSWER: u64 = u64::MAX;

impl SenderNetwork {
    /// The network thread of a sender as `settings` say, that sends from
    /// `socket` the frames handed over at `end`.
    #[must_use]
    pub fn new(socket: Socket, end: SenderEnd, settings: Settings) -> SenderNetwork {
        let stream = settings.stream;
        let samples = usize::from(settings.packet) * usize::from(stream.channels);
        SenderNetwork {
            socket,
            end,
            sender: Sender::new(stream, settings.timeline, settings.level),
            device: Device::new(stream.rate),
            origin: None,
            waiting: Vec::with_capacity(samples * 4),
            bytes: vec![0u8; packet::HEADER + samples * stream.format.bytes()].into_boxed_slice(),
            incoming: vec![0u8; 2_048].into_boxed_slice(),
            chooser: settings
                .choice
                .map(|choice| Chooser::new(choice, stream.window, stream.rate)),
            target: None,
            chosen: 0,
            settings,
            counts: SenderCounts::default(),
        }
    }

    /// What it has done so far.
    #[must_use]
    pub fn counts(&self) -> SenderCounts {
        self.counts
    }

    /// What the needs reported say about the assumptions that the choice of
    /// the level rests on; nothing if the level is held.
    #[must_use]
    pub fn checks(&self) -> Option<Checks> {
        self.chooser.as_ref().map(Chooser::checks)
    }

    /// The core's sender.
    #[must_use]
    pub fn sender(&self) -> &Sender {
        &self.sender
    }

    /// Waits up to `milliseconds` for something to do on the socket, then
    /// does all there is: sends the packets that the captured frames make,
    /// takes in departures, and answers reports.
    ///
    /// # Errors
    ///
    /// An error of the socket other than that nothing is waiting.
    pub fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        self.socket.wait(milliseconds)?;
        while let Some(captured) = self.end.full.take() {
            self.take_in(&captured);
            // The ring holds every buffer there is, so it has room for this.
            let _ = self.end.spare.put(captured.buffer);
            self.send_packets()?;
        }
        self.departures()?;
        self.answer()?;
        Ok(())
    }

    /// Takes in a cycle of the capture device.
    fn take_in(&mut self, captured: &Captured) {
        if captured.frames == 0 {
            return;
        }
        let channels = usize::from(self.settings.stream.channels);
        let Some(frames) = captured.buffer.get(..captured.frames * channels) else {
            return;
        };
        self.device.observe(captured.position, captured.time);
        let origin = *self.origin.get_or_insert(captured.position);
        // Where the cycle's first frame is in the timeline, against where
        // the next frame to be sent is.
        let expected = origin
            .saturating_add(self.sender.next())
            .saturating_add((self.waiting.len() / channels.max(1)) as u64);
        if captured.position < expected || captured.position - expected > LONGEST_GAP {
            self.restart(captured.position);
        } else if captured.position > expected {
            let missing = captured.position - expected;
            let samples = usize::try_from(missing).unwrap_or(0) * channels;
            self.waiting.resize(self.waiting.len() + samples, 0.0);
            self.counts.filled += missing;
        }
        self.waiting.extend_from_slice(frames);
    }

    /// Starts a timeline anew at the device's count `position`.
    fn restart(&mut self, position: u64) {
        self.waiting.clear();
        self.origin = Some(position);
        self.sender.restart(first_timeline());
        self.chosen = 0;
        self.counts.restarts += 1;
    }

    /// How much faster the capture device runs than its nominal rate against
    /// the host's clock, in parts per billion, by the line through its
    /// reports; zero while the line says nothing, or says more than a
    /// hundredth.
    fn drift(&self, position: u64) -> i32 {
        let rate = self.settings.stream.rate;
        let Some((_, duration)) = self.device.when_cycle(position, rate) else {
            return 0;
        };
        // A second at the nominal rate, in units of 2^-16 nanosecond.
        let nominal: i128 = 1_000_000_000 << 16;
        let measured = i128::from(duration);
        if measured <= 0 || (measured - nominal).abs() * 100 > nominal {
            return 0;
        }
        i32::try_from((nominal - measured) * 1_000_000_000 / measured).unwrap_or(0)
    }

    /// Sends the packets that the waiting frames make.
    fn send_packets(&mut self) -> io::Result<()> {
        let channels = usize::from(self.settings.stream.channels);
        let frames = usize::from(self.settings.packet);
        let samples = frames * channels;
        while self.waiting.len() >= samples && samples > 0 {
            let Some(origin) = self.origin else {
                return Ok(());
            };
            let first = self.sender.next();
            let position = origin.saturating_add(first);
            let Some(capture) = self.device.when(position) else {
                return Ok(());
            };
            self.steer();
            let drift = self.drift(position);
            let header = self.sender.packet(self.settings.packet, capture, drift);
            let length = self.write(&header, samples);
            self.waiting.drain(..samples);
            self.counts.packets += 1;
            let Some(length) = length else {
                continue;
            };
            let tag = tag(header.timeline, header.index);
            for &to in &self.settings.receivers {
                let bytes = self.bytes.get(..length).unwrap_or(&[]);
                match self.socket.send_to(bytes, to, tag) {
                    Ok(_) => {}
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        self.counts.unsent += 1;
                    }
                    Err(error) => return Err(error),
                }
            }
        }
        Ok(())
    }

    /// Ends a move of the level that has arrived, and chooses the level once
    /// for each second of stream: a move begins when the chooser finds one
    /// worth its cost.
    fn steer(&mut self) {
        let Some(chooser) = self.chooser.as_mut() else {
            return;
        };
        let rate = self.settings.stream.rate;
        let level = self.sender.current_level();
        if let Some(target) = self.target {
            // How far the level moves in one packet.
            let reach = i64::from(chooser.slope()).abs() * i64::from(self.settings.packet)
                / i64::from(rate.max(1));
            if (level - target).abs() <= reach {
                self.sender.level(target, 0);
                self.target = None;
            }
        }
        let next = self.sender.next();
        if next.saturating_sub(self.chosen) < u64::from(rate) {
            return;
        }
        self.chosen = next;
        if let Some(target) = chooser.choose(level) {
            let slope = if target > level {
                chooser.slope()
            } else {
                -chooser.slope()
            };
            self.sender.level(level, slope);
            self.target = Some(target);
            self.counts.moves += 1;
        }
    }

    /// Writes the packet with `header` and the first `samples` waiting
    /// samples, and returns its length.
    fn write(&mut self, header: &Audio, samples: usize) -> Option<usize> {
        let length = write_audio(header, &mut self.bytes)?;
        let payload = self.bytes.get_mut(packet::HEADER..length)?;
        let frames = self.waiting.get(..samples)?;
        match header.format {
            Format::Signed16 => to_signed16(frames, payload),
            Format::Signed24 => to_signed24(frames, payload),
        };
        Some(length)
    }

    /// Takes in when packets left.
    fn departures(&mut self) -> io::Result<()> {
        while let Some(departure) = self.socket.departure()? {
            if departure.tag == ANSWER {
                continue;
            }
            let timeline = self.sender.timeline();
            if departure.tag >> INDEX_BITS != timeline & ((1 << (64 - INDEX_BITS)) - 1) {
                continue;
            }
            let index = departure.tag & ((1 << INDEX_BITS) - 1);
            self.sender.departed(timeline, index, departure.stamp.time);
        }
        Ok(())
    }

    /// Answers the reports that arrived.
    fn answer(&mut self) -> io::Result<()> {
        let mut out = [0u8; packet::ECHO];
        while let Some(received) = self.socket.receive(&mut self.incoming)? {
            let Some(bytes) = self.incoming.get(..received.length) else {
                continue;
            };
            if packet::kind(bytes) != Ok(KIND_REPORT) {
                continue;
            }
            let Ok(report) = parse_report(bytes) else {
                continue;
            };
            if report.timeline == self.sender.timeline()
                && let Some(chooser) = self.chooser.as_mut()
            {
                chooser.observe(report.timeline, &parse_needs(bytes));
            }
            let Some(echo) = self.sender.answer(&report, received.arrival.time) else {
                continue;
            };
            let Some(length) = write_echo(&echo, &mut out) else {
                continue;
            };
            match self.socket.send_to(&out[..length], received.from, ANSWER) {
                Ok(_) => self.counts.answers += 1,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    self.counts.unsent += 1;
                }
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }
}

/// The tag of the departure of the packet of `timeline` whose first frame
/// has `index`.
fn tag(timeline: u64, index: u64) -> u64 {
    (timeline << INDEX_BITS) | (index & ((1 << INDEX_BITS) - 1))
}

/// A number for a timeline that is larger than that of any timeline begun
/// earlier on this host: the time of day in microseconds. A sender that
/// starts again therefore takes a larger number than before, and receivers
/// follow it at its second packet.
#[must_use]
pub fn first_timeline() -> u64 {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    u64::try_from(now.as_micros()).unwrap_or(u64::MAX)
}

/// The identity of the host's clock: the same for as long as the host runs,
/// and another after it starts again. On Linux it comes from the identity
/// the kernel gives each start of the system; elsewhere from the time of
/// day when this is first asked, which makes every start of the program a
/// new clock to its receivers.
#[must_use]
pub fn clock_identity() -> u32 {
    let text = std::fs::read_to_string("/proc/sys/kernel/random/boot_id").unwrap_or_default();
    let source = if text.trim().is_empty() {
        first_timeline().to_string()
    } else {
        text
    };
    // The FNV-1a hash of the text, folded to 32 bits.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in source.trim().bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    // The fold keeps the low 32 bits of the mixed halves.
    #[allow(clippy::cast_possible_truncation)]
    let folded = (hash ^ (hash >> 32)) as u32;
    folded
}
