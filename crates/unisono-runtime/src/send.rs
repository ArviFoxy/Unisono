// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Sender capture/network thread bridge, packetization, and transmission.
//!
//! Splits sender execution across two threads:
//! - The **capture thread** (owned by the audio backend) copies each captured
//!   block plus its device frame counter and timestamp into a preallocated
//!   ring buffer without locking or allocating.
//! - The **network thread** owns `unisono_core::sender::Sender`, the capture
//!   device clock regressor, the UDP socket, the retransmission ring, and the
//!   adaptive latency controller ([`crate::level`]). It packetizes audio,
//!   transmits to all configured receivers, records TX departure timestamps,
//!   answers receiver reports with echoes, and serves retransmission requests.
//!
//! Audio buffers are preallocated once and recycled through SPSC rings as in
//! [`crate::receive`]. If the network thread falls behind and no spare buffer
//! is available, the capture thread drops the cycle and increments its drop
//! counter.
//!
//! # Stream Index vs. Device Frame Counter
//!
//! Timeline frame indices count frames relative to the device counter at
//! timeline start. Dropped capture cycles are zero-filled so the timeline
//! index stays aligned with the device counter. If the device counter moves
//! backwards or jumps ahead by more than [`LONGEST_GAP`] frames, a new
//! timeline is started.

use std::io;
use std::net::SocketAddr;

use unisono_core::device::Device;
use unisono_core::packet::{
    self, Audio, Format, KIND_REPORT, KIND_REQUEST, PROTECTION_ON_REQUEST, Request, parse_needs,
    parse_report, parse_request, write_audio, write_echo,
};
use unisono_core::sender::{Sender, Settings as SenderSettings};
use unisono_dsp::format::{to_signed16, to_signed24};

use crate::InvalidSettings;
use crate::audio::Capture;
use crate::level::{Checks, Choice, Chooser};
use crate::network_thread::NetworkLoop;
use crate::ring::{Consumer, Producer, ring};
use crate::socket::{Socket, canonical_addr, is_restricted_send_error, is_transient_send_error};

/// The most frames that are sent as silence in place of dropped cycles. A
/// longer gap starts a timeline anew: 2^20 frames, about 22 seconds at
/// 48,000 frames a second.
pub const LONGEST_GAP: u64 = 1_048_576;

/// Maximum datagram size accepted for audio packets and allocated for receiver
/// datagram buffers, in bytes. Sharing one cap between sender validation and
/// receiver buffers ensures valid sender packets are never truncated on receipt.
pub const MAX_DATAGRAM: usize = 9_000;

/// Maximum incoming datagrams processed during one network turn so a burst
/// cannot starve audio packet emission.
const MAX_INCOMING_PER_TURN: usize = 256;

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
    /// How many of the last packets are kept, to be sent again to a
    /// receiver that asks for their frames; none for a stream without
    /// protection against loss.
    pub kept: usize,
}

impl Settings {
    /// Validates that the stream, packet size, level, retransmission cache,
    /// and adaptive level choice settings satisfy runtime invariants.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidSettings`] when any parameter is out of range or
    /// would overflow packet/cache sizing.
    pub fn validate(&self) -> Result<(), InvalidSettings> {
        if self.stream.rate == 0 {
            return Err(InvalidSettings::new("sample rate must be positive"));
        }
        if self.stream.channels == 0 {
            return Err(InvalidSettings::new("channel count must be positive"));
        }
        if self.stream.span == 0 {
            return Err(InvalidSettings::new(
                "clock estimator span must be positive",
            ));
        }
        if self.stream.window == 0 {
            return Err(InvalidSettings::new(
                "clock estimator window must be positive",
            ));
        }
        if self.packet == 0 {
            return Err(InvalidSettings::new("packet frame count must be positive"));
        }
        if self.level < 0 {
            return Err(InvalidSettings::new("initial level must be non-negative"));
        }
        let samples = usize::from(self.packet)
            .checked_mul(usize::from(self.stream.channels))
            .ok_or(InvalidSettings::new("packet sample count overflow"))?;
        let payload = samples
            .checked_mul(self.stream.format.bytes())
            .ok_or(InvalidSettings::new("packet payload size overflow"))?;
        let packet_bytes = packet::HEADER
            .checked_add(payload)
            .ok_or(InvalidSettings::new("packet size overflow"))?;
        if packet_bytes > MAX_DATAGRAM {
            return Err(InvalidSettings::new(
                "packet size exceeds maximum datagram size (9000 bytes)",
            ));
        }
        if self.kept.checked_mul(packet_bytes).is_none() {
            return Err(InvalidSettings::new("kept packet buffer size overflow"));
        }
        if let Some(choice) = self.choice {
            choice.validate()?;
        }
        Ok(())
    }
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
    /// Incoming datagrams ignored because their source address was not in the
    /// configured receiver list.
    pub ignored: u64,
    /// Datagrams that could not be sent due to a transient error.
    pub unsent: u64,
    /// Subset of `unsent` caused by per-destination policy (`EPERM`) or
    /// address availability (`EADDRNOTAVAIL`).
    pub blocked: u64,
    /// Moves of the level that were begun.
    pub moves: u64,
    /// Packets sent again to a receiver that asked for their frames.
    pub again: u64,
}

impl SenderCounts {
    /// Counts a transient send error, breaking out per-destination policy or
    /// address-availability failures (`EPERM`, `EADDRNOTAVAIL`) into `blocked`.
    fn record_unsent(&mut self, error: &io::Error) {
        self.unsent += 1;
        if is_restricted_send_error(error) {
            self.blocked += 1;
        }
    }
}

/// A packet that is kept to be sent again.
#[derive(Clone, Copy, Default)]
struct Kept {
    timeline: u64,
    /// Its first frame and the number of its frames.
    index: u64,
    frames: u16,
    /// Its length in bytes; zero where nothing is kept.
    length: usize,
}

/// An active ramp of the sender's latency level toward `target`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Ramp {
    target: i64,
    rising: bool,
}

/// The most packets that are sent again during one turn: a second of the
/// stream at five milliseconds a packet.
const MOST_AGAIN: usize = 200;

/// The network thread of a sender.
pub struct SenderNetwork {
    socket: Socket,
    end: SenderEnd,
    sender: Sender,
    /// The line through the capture device's reports.
    device: Device<64>,
    settings: Settings,
    /// Canonicalized receiver peer addresses for ingress filtering.
    allowed_receivers: Box<[SocketAddr]>,
    /// The device's count at the start of the timeline.
    origin: Option<u64>,
    /// Fixed-capacity buffer holding `< packet` leftover interleaved frames
    /// between capture cycles so sending never allocates even on huge gaps.
    pending: Box<[f32]>,
    pending_frames: usize,
    /// Where a packet is written.
    bytes: Box<[u8]>,
    /// Where datagrams are received.
    incoming: Box<[u8]>,
    /// What chooses the level, if it is chosen.
    chooser: Option<Chooser>,
    /// The active level ramp, while the level is moving.
    ramp: Option<Ramp>,
    /// The index of the next frame when the level was last chosen.
    chosen: u64,
    /// The last packets sent, each in as many bytes as a packet has at
    /// most, and what each is.
    kept: Box<[u8]>,
    places: Box<[Kept]>,
    /// The place that the next packet is kept at.
    place: usize,
    counts: SenderCounts,
}

/// The bits of a departure's tag that hold the index; the bits above hold
/// the low bits of the timeline's number, so that a departure of a timeline
/// before is told apart.
const INDEX_BITS: u32 = 48;

impl SenderNetwork {
    /// The network thread of a sender as `settings` say, that sends from
    /// `socket` the frames handed over at `end`.
    #[must_use]
    pub fn new(socket: Socket, end: SenderEnd, settings: Settings) -> SenderNetwork {
        let stream = settings.stream;
        let samples = usize::from(settings.packet).saturating_mul(usize::from(stream.channels));
        let packet_bytes =
            packet::HEADER.saturating_add(samples.saturating_mul(stream.format.bytes()));
        let allowed_receivers = settings
            .receivers
            .iter()
            .copied()
            .map(canonical_addr)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        SenderNetwork {
            socket,
            end,
            sender: Sender::new(stream, settings.timeline, settings.level),
            device: Device::new(stream.rate),
            allowed_receivers,
            origin: None,
            pending: vec![0.0f32; samples].into_boxed_slice(),
            pending_frames: 0,
            bytes: vec![0u8; packet_bytes].into_boxed_slice(),
            incoming: vec![0u8; 2_048].into_boxed_slice(),
            chooser: settings
                .choice
                .map(|choice| Chooser::new(choice, stream.window, stream.rate)),
            ramp: None,
            chosen: 0,
            kept: vec![0u8; settings.kept.saturating_mul(packet_bytes)].into_boxed_slice(),
            places: vec![Kept::default(); settings.kept].into_boxed_slice(),
            place: 0,
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

    /// Waits up to `milliseconds` for something to do on the socket (unless
    /// captured audio is already queued), then does all there is: sends the
    /// packets that the captured frames make, takes in departures, and answers
    /// reports.
    ///
    /// # Errors
    ///
    /// A fatal error of the socket.
    pub fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        let wait_ms = if self.end.full.waiting() > 0 {
            0
        } else {
            milliseconds
        };
        self.socket.wait(wait_ms)?;
        while let Some(captured) = self.end.full.take() {
            let result = self.take_in_and_send(&captured);
            // The ring holds every buffer there is, so it has room for this.
            let _ = self.end.spare.put(captured.buffer);
            result?;
        }
        self.departures()?;
        self.answer()?;
        Ok(())
    }

    /// Takes in a cycle of the capture device and emits every full packet
    /// without allocating.
    fn take_in_and_send(&mut self, captured: &Captured) -> io::Result<()> {
        let packet_frames = usize::from(self.settings.packet);
        let channels = usize::from(self.settings.stream.channels);
        if captured.frames == 0
            || packet_frames == 0
            || channels == 0
            || self.settings.stream.rate == 0
        {
            return Ok(());
        }
        let Some(total_samples) = captured.frames.checked_mul(channels) else {
            return Ok(());
        };
        let Some(frames) = captured.buffer.get(..total_samples) else {
            return Ok(());
        };
        self.device.observe(captured.position, captured.time);
        let origin = *self.origin.get_or_insert(captured.position);
        // Where the cycle's first frame is in the timeline, against where
        // the next frame to be sent is.
        let expected = origin
            .saturating_add(self.sender.next())
            .saturating_add(self.pending_frames as u64);
        if captured.position < expected || captured.position - expected > LONGEST_GAP {
            self.restart(captured.position);
        } else if captured.position > expected {
            let mut missing = captured.position - expected;
            self.counts.filled += missing;
            while missing > 0 {
                let room = packet_frames - self.pending_frames;
                let take = usize::try_from(missing).unwrap_or(usize::MAX).min(room);
                let start = self.pending_frames * channels;
                if let Some(slot) = self.pending.get_mut(start..start + take * channels) {
                    slot.fill(0.0);
                }
                self.pending_frames += take;
                missing -= take as u64;
                if self.pending_frames == packet_frames {
                    self.pending_frames = 0;
                    self.emit_packet(None)?;
                }
            }
        }
        let mut offset = 0usize;
        if self.pending_frames > 0 {
            let take = (packet_frames - self.pending_frames).min(captured.frames);
            let dst_start = self.pending_frames * channels;
            if let (Some(dst), Some(src)) = (
                self.pending.get_mut(dst_start..dst_start + take * channels),
                frames.get(..take * channels),
            ) {
                dst.copy_from_slice(src);
            }
            self.pending_frames += take;
            offset += take;
            if self.pending_frames == packet_frames {
                self.pending_frames = 0;
                self.emit_packet(None)?;
            }
        }
        while captured.frames - offset >= packet_frames {
            let start = offset * channels;
            if let Some(chunk) = frames.get(start..start + packet_frames * channels) {
                self.emit_packet(Some(chunk))?;
            }
            offset += packet_frames;
        }
        let leftover = captured.frames - offset;
        if leftover > 0 {
            if let (Some(dst), Some(src)) = (
                self.pending.get_mut(..leftover * channels),
                frames.get(offset * channels..captured.frames * channels),
            ) {
                dst.copy_from_slice(src);
            }
            self.pending_frames = leftover;
        }
        Ok(())
    }

    /// Starts a timeline anew at the device's count `position`.
    fn restart(&mut self, position: u64) {
        self.pending_frames = 0;
        self.origin = Some(position);
        self.sender.restart(first_timeline());
        // Stop any in-progress ramp cleanly on timeline restart.
        let level = self.sender.current_level();
        self.sender.level(level, 0);
        self.ramp = None;
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

    /// Encodes and transmits one packet from `external` (or `self.pending`
    /// when `external` is `None`). Only the first successful receiver send is
    /// tagged for departure timestamping so multiple receivers do not
    /// overwrite `stamped_departure`.
    fn emit_packet(&mut self, external: Option<&[f32]>) -> io::Result<()> {
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
        let mut header = self.sender.packet(self.settings.packet, capture, drift);
        if !self.places.is_empty() {
            header.protection = PROTECTION_ON_REQUEST;
        }
        let length = self.write(&header, external);
        self.counts.packets += 1;
        let Some(length) = length else {
            return Ok(());
        };
        self.remember(&header, length);
        let packet_tag = tag(header.timeline, header.index);
        let mut tagged = false;
        for &to in &self.settings.receivers {
            let bytes = self.bytes.get(..length).unwrap_or(&[]);
            let sent = if tagged {
                self.socket.send_untagged(bytes, to)
            } else {
                self.socket.send_to(bytes, to, packet_tag)
            };
            match sent {
                Ok(_) => tagged = true,
                Err(error) if is_transient_send_error(&error) => {
                    self.counts.record_unsent(&error);
                }
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }

    /// Ends a move of the level that has arrived or crossed its target, and
    /// chooses the level once for each second of stream: a move begins when
    /// the chooser finds one worth its cost.
    fn steer(&mut self) {
        let Some(chooser) = self.chooser.as_mut() else {
            return;
        };
        let slope = chooser.slope();
        if slope <= 0 {
            return;
        }
        let rate = self.settings.stream.rate.max(1);
        let mut level = self.sender.current_level();
        if let Some(ramp) = self.ramp {
            // How far the level moves in one packet.
            let reach = u64::try_from(
                i128::from(slope) * i128::from(self.settings.packet) / i128::from(rate),
            )
            .unwrap_or(u64::MAX);
            let crossed = if ramp.rising {
                level >= ramp.target
            } else {
                level <= ramp.target
            };
            if crossed || level.abs_diff(ramp.target) <= reach {
                self.sender.level(ramp.target, 0);
                self.ramp = None;
                level = ramp.target;
            }
        }
        let next = self.sender.next();
        if next.saturating_sub(self.chosen) < u64::from(rate) {
            return;
        }
        self.chosen = next;
        if let Some(target) = chooser.choose(level) {
            if target == level || self.ramp.is_some_and(|ramp| ramp.target == target) {
                return;
            }
            let rising = target > level;
            let signed_slope = if rising { slope } else { -slope };
            self.sender.level(level, signed_slope);
            self.ramp = Some(Ramp { target, rising });
            self.counts.moves += 1;
        }
    }

    /// Writes the packet with `header` and either `external` or the samples in
    /// `self.pending`, and returns its length.
    fn write(&mut self, header: &Audio, external: Option<&[f32]>) -> Option<usize> {
        let samples = usize::from(self.settings.packet)
            .checked_mul(usize::from(self.settings.stream.channels))?;
        let length = write_audio(header, &mut self.bytes)?;
        let payload = self.bytes.get_mut(packet::HEADER..length)?;
        let frames = match external {
            Some(slice) => slice.get(..samples)?,
            None => self.pending.get(..samples)?,
        };
        match header.format {
            Format::Signed16 => to_signed16(frames, payload),
            Format::Signed24 => to_signed24(frames, payload),
        };
        Some(length)
    }

    /// Takes in when packets left.
    fn departures(&mut self) -> io::Result<()> {
        while let Some(departure) = self.socket.departure()? {
            let timeline = self.sender.timeline();
            if departure.tag >> INDEX_BITS != timeline & ((1 << (64 - INDEX_BITS)) - 1) {
                continue;
            }
            let index = departure.tag & ((1 << INDEX_BITS) - 1);
            self.sender.departed(timeline, index, departure.stamp.time);
        }
        Ok(())
    }

    /// Keeps the packet with `header`, whose `length` bytes were just
    /// written, in the place of the oldest packet kept.
    fn remember(&mut self, header: &Audio, length: usize) {
        let room = self.bytes.len();
        let Some(slot) = self.places.get_mut(self.place) else {
            return;
        };
        let from = self.place * room;
        if let (Some(to), Some(bytes)) = (
            self.kept.get_mut(from..from + length),
            self.bytes.get(..length),
        ) {
            to.copy_from_slice(bytes);
            *slot = Kept {
                timeline: header.timeline,
                index: header.index,
                frames: header.frames,
                length,
            };
            self.place = (self.place + 1) % self.places.len();
        }
    }

    /// Sends the kept packets with frames that `request` names again to the
    /// receiver at `to`, oldest first, up to the per-turn retransmission cap.
    fn again(
        &mut self,
        request: &Request,
        to: SocketAddr,
        sent_total: &mut usize,
    ) -> io::Result<()> {
        if request.stream != self.settings.stream.stream || *sent_total >= MOST_AGAIN {
            return Ok(());
        }
        let room = self.bytes.len();
        let end = request.first.saturating_add(request.frames);
        for step in 0..self.places.len() {
            if *sent_total >= MOST_AGAIN {
                break;
            }
            let place = (self.place + step) % self.places.len();
            let Some(kept) = self.places.get(place).copied() else {
                continue;
            };
            let named = kept.length > 0
                && kept.timeline == request.timeline
                && kept.index < end
                && kept.index.saturating_add(u64::from(kept.frames)) > request.first;
            if !named {
                continue;
            }
            let bytes = self
                .kept
                .get(place * room..place * room + kept.length)
                .unwrap_or(&[]);
            match self.socket.send_untagged(bytes, to) {
                Ok(_) => self.counts.again += 1,
                Err(error) if is_transient_send_error(&error) => {
                    self.counts.record_unsent(&error);
                }
                Err(error) => return Err(error),
            }
            *sent_total += 1;
        }
        Ok(())
    }

    /// Answers the reports that arrived from configured receivers on this
    /// stream, and sends again what those receivers ask for.
    fn answer(&mut self) -> io::Result<()> {
        let mut out = [0u8; packet::ECHO];
        let mut turn_again = 0usize;
        for _ in 0..MAX_INCOMING_PER_TURN {
            let Some(received) = self.socket.receive(&mut self.incoming)? else {
                break;
            };
            let peer = canonical_addr(received.from);
            if !self.allowed_receivers.contains(&peer) {
                self.counts.ignored += 1;
                continue;
            }
            let Some(bytes) = self.incoming.get(..received.length) else {
                continue;
            };
            if packet::kind(bytes) == Ok(KIND_REQUEST) {
                if let Ok(request) = parse_request(bytes) {
                    self.again(&request, received.from, &mut turn_again)?;
                }
                continue;
            }
            if packet::kind(bytes) != Ok(KIND_REPORT) {
                continue;
            }
            let Ok(report) = parse_report(bytes) else {
                continue;
            };
            if report.stream != self.settings.stream.stream {
                continue;
            }
            if report.timeline == self.sender.timeline()
                && self.sender.next() > 0
                && let Some(chooser) = self.chooser.as_mut()
            {
                let max_stretch =
                    (self.sender.next() - 1) / u64::from(self.settings.stream.window.max(1));
                chooser.observe_up_to(report.timeline, &parse_needs(bytes), max_stretch);
            }
            let Some(echo) = self.sender.answer(&report, received.arrival.time) else {
                continue;
            };
            let Some(length) = write_echo(&echo, &mut out) else {
                continue;
            };
            match self.socket.send_untagged(&out[..length], received.from) {
                Ok(_) => self.counts.answers += 1,
                Err(error) if is_transient_send_error(&error) => {
                    self.counts.record_unsent(&error);
                }
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }
}

impl NetworkLoop for SenderNetwork {
    fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        SenderNetwork::turn(self, milliseconds)
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

#[cfg(test)]
mod tests {
    use std::net::{SocketAddr, UdpSocket};
    use std::time::Duration;

    use unisono_core::packet::{self, Format, Recent, Report, write_needs, write_report};
    use unisono_core::sender::Settings as StreamSettings;

    use super::{Ramp, SenderNetwork, Settings, link};
    use crate::audio::Capture;
    use crate::level::{Choice, Weights};
    use crate::socket::Socket;

    fn base_settings(receivers: Vec<SocketAddr>, choice: Option<Choice>) -> Settings {
        Settings {
            stream: StreamSettings {
                stream: 7,
                rate: 48_000,
                channels: 2,
                format: Format::Signed24,
                span: 2_000,
                window: 2_400,
                clock: 1,
            },
            packet: 240,
            level: 30_000_000,
            choice,
            timeline: 10,
            receivers,
            kept: 8,
        }
    }

    #[test]
    fn settings_validation_rejects_invalid_stream_packet_and_choice() {
        let valid = base_settings(Vec::new(), None);
        assert!(valid.validate().is_ok());

        let mut bad = valid.clone();
        bad.stream.rate = 0;
        assert!(bad.validate().is_err());

        let mut bad = valid.clone();
        bad.packet = 0;
        assert!(bad.validate().is_err());

        let mut bad = valid.clone();
        bad.level = -1;
        assert!(bad.validate().is_err());

        let mut bad = valid.clone();
        bad.packet = 1_500; // 88 + 1500 * 2 * 3 = 9088 > MAX_DATAGRAM (9000)
        assert!(bad.validate().is_err());

        let mut at_cap = valid;
        at_cap.packet = 1_485; // 88 + 1485 * 2 * 3 = 8998 <= MAX_DATAGRAM (9000)
        assert!(at_cap.validate().is_ok());
    }

    #[test]
    fn unknown_peer_and_wrong_stream_reports_are_ignored_before_chooser_and_echo() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let receiver = UdpSocket::bind(loopback).expect("receiver");
        receiver
            .set_read_timeout(Some(Duration::from_millis(50)))
            .expect("timeout");
        let stranger = UdpSocket::bind(loopback).expect("stranger");
        stranger
            .set_read_timeout(Some(Duration::from_millis(50)))
            .expect("timeout");

        let sender_socket = Socket::bind(loopback).expect("sender socket");
        let sender_addr = sender_socket.address().expect("addr");
        let (mut capture_end, sender_end) = link(4, 240, 2);
        let choice = Choice {
            weights: Weights {
                latency: 1_000.0,
                target: 0,
                off_target: 0.0,
                gap: 600.0,
                missed: 60_000.0,
                moving: 60.0,
            },
            history: 64,
            slope: 1_000_000,
        };
        let mut sender = SenderNetwork::new(
            sender_socket,
            sender_end,
            base_settings(vec![receiver.local_addr().expect("addr")], Some(choice)),
        );
        // Emit one packet so sender.next() > 0.
        capture_end.cycle(&[0.0f32; 480], 0, 1_000_000);
        sender.turn(0).expect("turn");

        let mut buf = [0u8; 128];
        let mut recent = Recent::NONE;
        recent.count = 1;
        recent.newest = 0;
        recent.needs[0] = 5_000;

        // 1. Report from an unknown peer on the right stream -> ignored.
        let report = Report {
            stream: 7,
            timeline: 10,
            receiver: 1,
            sequence: 1,
        };
        let len = write_report(&report, &mut buf, 128).expect("report");
        assert!(write_needs(&recent, &mut buf[..len]));
        stranger.send_to(&buf[..len], sender_addr).expect("send");
        sender.turn(0).expect("turn");
        assert_eq!(sender.counts().answers, 0);
        assert_eq!(sender.counts().ignored, 1);

        // 2. Report from the known receiver on a wrong stream -> ignored.
        let wrong_stream = Report {
            stream: 99,
            ..report
        };
        let len = write_report(&wrong_stream, &mut buf, 128).expect("report");
        assert!(write_needs(&recent, &mut buf[..len]));
        receiver.send_to(&buf[..len], sender_addr).expect("send");
        sender.turn(0).expect("turn");
        assert_eq!(sender.counts().answers, 0);

        // 3. Report from the known receiver on the right stream -> answered.
        let len = write_report(&report, &mut buf, 128).expect("report");
        assert!(write_needs(&recent, &mut buf[..len]));
        receiver.send_to(&buf[..len], sender_addr).expect("send");
        sender.turn(0).expect("turn");
        assert_eq!(sender.counts().answers, 1);
    }

    #[test]
    fn steer_snaps_when_crossing_target_even_with_zero_per_packet_reach() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let sender_socket = Socket::bind(loopback).expect("sender socket");
        let (mut capture_end, sender_end) = link(4, 240, 2);
        // slope * packet / rate = 100 * 240 / 48000 = 0 (integer division).
        let choice = Choice {
            weights: Weights {
                latency: 1_000.0,
                target: 0,
                off_target: 0.0,
                gap: 600.0,
                missed: 60_000.0,
                moving: 60.0,
            },
            history: 64,
            slope: 100,
        };
        let mut sender = SenderNetwork::new(
            sender_socket,
            sender_end,
            base_settings(Vec::new(), Some(choice)),
        );
        // Simulate a rising ramp that has crossed its target by 1 ns.
        sender.sender.level(30_000_001, 100);
        sender.ramp = Some(Ramp {
            target: 30_000_000,
            rising: true,
        });
        capture_end.cycle(&[0.0f32; 480], 0, 1_000_000);
        sender.turn(0).expect("turn");
        assert_eq!(sender.ramp, None);
        assert_eq!(sender.sender().current_level(), 30_000_000);
    }

    #[test]
    fn capture_gap_fills_silence_without_resizing_and_keeps_index_aligned() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let receiver = UdpSocket::bind(loopback).expect("receiver");
        let sender_socket = Socket::bind(loopback).expect("sender socket");
        let (mut capture_end, sender_end) = link(4, 256, 2);
        let mut sender = SenderNetwork::new(
            sender_socket,
            sender_end,
            base_settings(vec![receiver.local_addr().expect("addr")], None),
        );
        // First cycle: 256 frames (1 packet of 240 + 16 pending).
        capture_end.cycle(&[0.25f32; 512], 0, 1_000_000);
        sender.turn(0).expect("turn 1");
        assert_eq!(sender.counts().packets, 1);
        assert_eq!(sender.pending_frames, 16);

        // Next cycle jumps ahead by 720 dropped frames (position 976 = 256 + 720).
        capture_end.cycle(&[0.5f32; 512], 976, 21_333_333);
        sender.turn(0).expect("turn 2");
        assert_eq!(sender.counts().filled, 720);
        assert_eq!(sender.counts().restarts, 0);
        // Total frames covered = 976 + 256 = 1232 => 5 full packets (1200) + 32 pending.
        assert_eq!(sender.counts().packets, 5);
        assert_eq!(sender.pending_frames, 32);
    }

    #[test]
    fn multi_receiver_send_produces_one_packet_per_receiver_with_single_departure_tag() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let r1 = UdpSocket::bind(loopback).expect("r1");
        let r2 = UdpSocket::bind(loopback).expect("r2");
        r1.set_read_timeout(Some(Duration::from_secs(1)))
            .expect("timeout");
        r2.set_read_timeout(Some(Duration::from_secs(1)))
            .expect("timeout");
        let sender_socket = Socket::bind(loopback).expect("sender socket");
        let (mut capture_end, sender_end) = link(4, 240, 2);
        let mut sender = SenderNetwork::new(
            sender_socket,
            sender_end,
            base_settings(
                vec![r1.local_addr().expect("r1"), r2.local_addr().expect("r2")],
                None,
            ),
        );
        capture_end.cycle(&[0.1f32; 480], 0, 1_000_000);
        sender.turn(0).expect("turn");
        let mut b1 = [0u8; 2048];
        let mut b2 = [0u8; 2048];
        let (l1, _) = r1.recv_from(&mut b1).expect("r1 recv");
        let (l2, _) = r2.recv_from(&mut b2).expect("r2 recv");
        assert_eq!(l1, l2);
        assert!(packet::parse_audio(&b1[..l1]).is_ok());
    }
}
