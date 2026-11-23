// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Receiver network/audio thread bridge, pure network sync engine, and
//! lock-free ring transport.
//!
//! A receiver splits work across two threads:
//! - The **network thread** owns the UDP socket, [`ReceiverNetEngine`] (with
//!   [`unisono_core::sync::Sync`] in peer/star mode), parses incoming
//!   datagrams with kernel arrival timestamps, sends reports, peer probes,
//!   peer link-state relays, and retransmission requests, and collects TX
//!   departure timestamps.
//! - The **audio thread** owns `unisono_core::receiver::Receiver`, the sample
//!   store, and the resampler pump inside [`ReceiverPlayback`]. Keeping the
//!   core state machine single-threaded preserves all Lean proof invariants.
//!
//! Preallocated SPSC rings ([`crate::ring`]) pass messages without locks or
//! heap allocations after startup:
//! - network -> audio: [`Incoming`] audio packets, `SyncSnapshot` updates (in
//!   peer/star mode), or legacy report echoes and TX departure timestamps (in
//!   hull mode);
//! - audio -> network: [`Outgoing`] reports and need summaries;
//! - audio -> network: recycled packet buffers.
//!
//! Each audio callback drains at most a bounded number of incoming items so
//! per-cycle execution time remains strictly bounded (checked by
//! `crates/cycle-cost`).

use std::io;
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU32, AtomicU64, Ordering};

use unisono_core::packet::{
    self, Audio, Echo, KIND_AUDIO, KIND_ECHO, KIND_PEER_ECHO, KIND_PEER_PROBE, KIND_PEER_RELAY,
    Recent, Report, Request, parse_audio, parse_echo, parse_peer_echo, parse_peer_probe,
    parse_peer_relay, write_needs, write_peer_echo, write_peer_probe, write_peer_relay,
    write_report, write_request,
};
use unisono_core::sync::{
    DEFAULT_RELAY_INTERVAL_NS, MAX_DIRECT_PEERS, Sync, SyncSettings, SyncSnapshot, WEIGHT_UNITY_Q16,
};

use crate::InvalidSettings;
use crate::audio::Playback;
use crate::clock;
use crate::network_thread::NetworkLoop;
use crate::pump::ReceiverPlayback;
use crate::retransmission::RetransmissionTracker;
use crate::ring::{Consumer, Producer, ring};
use crate::socket::{DatagramSink, SendStatus, Socket, SocketSink, canonical_addr};

/// Maximum datagrams drained in one [`ReceiverNetwork::turn`] so a burst
/// cannot starve departures, reports, peer probes, or retransmission requests.
const MAX_RECEIVE_PER_TURN: usize = 256;

/// Bit 63 of a TX departure tag marks a `PeerProbe`; bit 63 clear marks a
/// sender `Report`.
const PEER_PROBE_TAG_BIT: u64 = 1 << 63;

/// Bit shift for the peer slot index inside a `PeerProbe` TX departure tag.
const PEER_IDX_SHIFT: u32 = 56;

/// Mask for the 7-bit peer slot index (`0..128`, covering `MAX_DIRECT_PEERS`).
const PEER_IDX_MASK: u64 = 0x7f;

/// Mask for the 56-bit probe sequence inside a `PeerProbe` TX departure tag.
const PEER_SEQ_MASK: u64 = (1u64 << PEER_IDX_SHIFT) - 1;

/// Clock synchronization estimator mode for a receiver.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SyncMode {
    /// Unified Kalman + BLUE + min-RTT synchronization ([`Sync`]). Operates in
    /// Star mode when zero peers are configured or reachable, and activates
    /// peer-assisted BLUE + modal control whenever peers are active.
    #[default]
    Peer,
    /// Legacy one-way lower-hull clock estimator running directly on the audio
    /// thread (no peer-to-peer exchanges).
    Hull,
}

/// Static configuration for one direct receiver peer in [`SyncMode::Peer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PeerConfig {
    /// Non-zero unique receiver identity of the peer.
    pub identity: u64,
    /// UDP socket address of the peer's receiver socket.
    pub address: SocketAddr,
    /// Optional Q16 static link-weight multiplier (`WEIGHT_UNITY_Q16 = 65_536`
    /// for `1.0`). Zero is normalized to unity.
    pub weight_q16: u32,
}

/// Configuration for [`ReceiverNetEngine`] and [`ReceiverNetwork::with_config`].
#[derive(Clone, Debug)]
pub struct NetConfig {
    /// Stream identifier accepted by this receiver.
    pub stream: u16,
    /// Synchronization engine mode (`Peer` default, `Hull` legacy).
    pub sync_mode: SyncMode,
    /// [`Sync`] settings used when `sync_mode == SyncMode::Peer`.
    pub sync_settings: SyncSettings,
    /// Optional Q16 static link-weight multiplier for the direct sender link
    /// (`WEIGHT_UNITY_Q16 = 65_536` for `1.0`).
    pub sender_weight_q16: u32,
    /// Static allowlist of direct peer receivers (must be empty in `Hull` mode).
    pub peers: Vec<PeerConfig>,
    /// Maximum UDP datagram buffer size, in bytes.
    pub datagram: usize,
}

impl NetConfig {
    /// Legacy lower-hull configuration with no peer exchanges.
    #[must_use]
    pub fn hull(stream: u16, datagram: usize) -> NetConfig {
        NetConfig {
            stream,
            sync_mode: SyncMode::Hull,
            sync_settings: SyncSettings::standard(stream, 1),
            sender_weight_q16: WEIGHT_UNITY_Q16,
            peers: Vec::new(),
            datagram,
        }
    }

    /// Standard unified peer/star configuration with zero initial peers.
    #[must_use]
    pub fn peer(stream: u16, identity: u64, datagram: usize) -> NetConfig {
        NetConfig {
            stream,
            sync_mode: SyncMode::Peer,
            sync_settings: SyncSettings::standard(stream, identity),
            sender_weight_q16: WEIGHT_UNITY_Q16,
            peers: Vec::new(),
            datagram,
        }
    }

    /// Validates peer allowlist uniqueness, stream/identity consistency, and
    /// [`SyncSettings`] bounds.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidSettings`] when any configuration field violates
    /// runtime or protocol invariants.
    pub fn validate(&self) -> Result<(), InvalidSettings> {
        if self.datagram < packet::HEADER {
            return Err(InvalidSettings::new(
                "datagram buffer size must be at least the audio header size",
            ));
        }
        match self.sync_mode {
            SyncMode::Hull => {
                if !self.peers.is_empty() {
                    return Err(InvalidSettings::new(
                        "peers cannot be configured in hull sync mode",
                    ));
                }
            }
            SyncMode::Peer => {
                let s = &self.sync_settings;
                if s.stream != self.stream {
                    return Err(InvalidSettings::new(
                        "sync stream identifier must match receiver stream",
                    ));
                }
                if s.identity == 0 {
                    return Err(InvalidSettings::new(
                        "receiver identity must be non-zero in peer sync mode",
                    ));
                }
                if s.variance_floor_ns2 == 0 || s.initial_variance_ns2 == 0 {
                    return Err(InvalidSettings::new(
                        "sync variance parameters must be positive",
                    ));
                }
                if s.jump_ns < 0 {
                    return Err(InvalidSettings::new(
                        "sync jump threshold must be non-negative",
                    ));
                }
                if s.peer_stale_ns <= 0
                    || s.startup_probe_ns <= 0
                    || s.steady_probe_ns <= 0
                    || s.relay_interval_ns <= 0
                    || s.startup_duration_ns < 0
                {
                    return Err(InvalidSettings::new(
                        "sync probe, relay, and staleness intervals must be positive",
                    ));
                }
                if self.peers.len() > MAX_DIRECT_PEERS {
                    return Err(InvalidSettings::new(
                        "configured peer count exceeds maximum direct peers (15)",
                    ));
                }
                for (i, peer) in self.peers.iter().enumerate() {
                    if peer.identity == 0 {
                        return Err(InvalidSettings::new("peer identity must be non-zero"));
                    }
                    if peer.identity == s.identity {
                        return Err(InvalidSettings::new(
                            "peer identity must not match this receiver's identity",
                        ));
                    }
                    let addr_i = canonical_addr(peer.address);
                    for other in &self.peers[i + 1..] {
                        if other.identity == peer.identity {
                            return Err(InvalidSettings::new("duplicate peer identity"));
                        }
                        if canonical_addr(other.address) == addr_i {
                            return Err(InvalidSettings::new("duplicate peer socket address"));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// Snapshot of audio-thread confirmation state passed into
/// [`ReceiverNetEngine`] so the engine runs identically with live atomic
/// handoff ([`ReceiverNetwork`]) and deterministic simulators.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConfirmedState {
    /// Whether an audio consumer is attached to confirm timelines. When
    /// `false`, the network engine adopts timelines directly from accepted
    /// audio packets.
    pub attached: bool,
    /// Whether the audio consumer has confirmed an active timeline.
    pub active: bool,
    /// Confirmed timeline identifier (valid when `active` is `true`).
    pub timeline: u64,
    /// Confirmed sender clock identifier (valid when `active` is `true`).
    pub clock_id: u32,
    /// Expected stream sample rate, or `0` to accept any rate.
    pub rate: u32,
    /// Expected stream channel count, or `0` to accept any channel count.
    pub channels: u8,
}

impl ConfirmedState {
    /// State when no audio thread is attached.
    pub const UNATTACHED: ConfirmedState = ConfirmedState {
        attached: false,
        active: false,
        timeline: 0,
        clock_id: 0,
        rate: 0,
        channels: 0,
    };
}

/// Outcome of [`ReceiverNetEngine::on_datagram`] indicating what, if anything,
/// the caller should forward to the audio thread.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DatagramAction {
    /// Handled completely on the network side (peer sync, v2 sender echo in
    /// peer mode, rejected datagram, or dropped audio under backpressure).
    Consumed,
    /// Valid audio packet matching stream and format; forward to the audio
    /// thread with its arrival timestamp.
    Audio(Audio),
    /// Valid sender echo in legacy hull mode; forward to the audio thread.
    HullEcho(Echo),
}

/// Lock-free state published by the audio thread to the network thread so the
/// network thread updates its active sender, sender clock identity, packet
/// padding length, and retransmission tracker only for confirmed timelines and
/// matching formats.
struct Confirmed {
    attached: AtomicBool,
    active: AtomicBool,
    timeline: AtomicU64,
    clock_id: AtomicU32,
    rate: AtomicU32,
    channels: AtomicU8,
}

impl Confirmed {
    fn new() -> Confirmed {
        Confirmed {
            attached: AtomicBool::new(false),
            active: AtomicBool::new(false),
            timeline: AtomicU64::new(0),
            clock_id: AtomicU32::new(0),
            rate: AtomicU32::new(0),
            channels: AtomicU8::new(0),
        }
    }

    /// Reads a consistent [`ConfirmedState`] snapshot without locking.
    fn load(&self) -> ConfirmedState {
        let attached = self.attached.load(Ordering::Acquire);
        let rate = self.rate.load(Ordering::Acquire);
        let channels = self.channels.load(Ordering::Acquire);
        let active = self.active.load(Ordering::Acquire);
        if !active {
            return ConfirmedState {
                attached,
                active: false,
                timeline: 0,
                clock_id: 0,
                rate,
                channels,
            };
        }
        // Retry if `timeline` changed mid-read so `(timeline, clock_id)` come
        // from the same audio-thread publication.
        let mut timeline = self.timeline.load(Ordering::Acquire);
        let mut clock_id = self.clock_id.load(Ordering::Acquire);
        for _ in 0..4 {
            let check = self.timeline.load(Ordering::Acquire);
            if check == timeline {
                break;
            }
            timeline = check;
            clock_id = self.clock_id.load(Ordering::Acquire);
        }
        ConfirmedState {
            attached,
            active: true,
            timeline,
            clock_id,
            rate,
            channels,
        }
    }
}

/// Candidate sender metadata cached while waiting for the audio thread to
/// confirm a newly observed timeline, including its own
/// [`RetransmissionTracker`] so contiguous packets arriving before adoption do
/// not trigger spurious retransmission requests while missing frames are still
/// tracked.
#[derive(Clone, Copy)]
struct PendingSender {
    timeline: u64,
    clock_id: u32,
    from: SocketAddr,
    length: usize,
    retransmission: RetransmissionTracker,
}

/// Prevalidated peer allowlist entry mapping one canonical socket address to
/// one receiver identity and [`Sync`] slot index.
#[derive(Clone, Copy, Debug)]
struct AllowedPeer {
    identity: u64,
    address: SocketAddr,
    canonical: SocketAddr,
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
    /// The sender's answer to a report (used in legacy hull mode).
    Answer(Echo),
    /// A report left (used in legacy hull mode).
    Departed {
        /// Its sequence number.
        sequence: u64,
        /// The reading of the raw clock when it left.
        time: i64,
    },
    /// Wait-free clock synchronization snapshot published by [`Sync`] on the
    /// network thread, fenced by `clock_id` so pre-reboot snapshots are
    /// discarded after a sender clock change.
    SyncUpdate {
        /// Sender clock identifier for which `snapshot` was computed.
        clock_id: u32,
        /// Latest [`SyncSnapshot`] from [`Sync`].
        snapshot: SyncSnapshot,
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
    /// The most answers, departures, sync snapshots, and reports that can wait
    /// at once.
    pub messages: usize,
}

/// Shipped ring sizes shared by the CLI, C library, and simulator.
pub const SHIPPED_SIZES: Sizes = Sizes {
    buffers: 64,
    datagram: crate::send::MAX_DATAGRAM,
    messages: 64,
};

/// Maximum incoming ring items drained per shipped audio callback.
pub const SHIPPED_INTAKE_ITEMS: usize = 16;

/// Shipped receiver audio-thread wrapper matching
/// [`crate::pump::ShippedPlayback`].
pub type ShippedAudio = ReceiverAudio<256, 64, 8, 64>;

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
    /// Answers to reports handled (forwarded to audio thread in hull mode or
    /// consumed by [`Sync`] in peer mode).
    pub answers: u64,
    /// Reports sent.
    pub reports: u64,
    /// Requests sent for frames to be sent again.
    pub requests: u64,
    /// Outgoing datagrams dropped due to a transient send error.
    pub unsent: u64,
    /// Subset of `unsent` caused by per-destination policy (`EPERM`) or
    /// address availability (`EADDRNOTAVAIL`).
    pub blocked: u64,
    /// Datagrams or snapshots dropped because the audio thread had not handed
    /// back a buffer, or had no room for another item.
    pub dropped: u64,
    /// Datagrams rejected as invalid, wrong stream/format, or unauthorized
    /// source.
    pub other: u64,
    /// Peer-to-peer clock probes sent.
    pub peer_probes_sent: u64,
    /// Peer-to-peer clock probes answered with a `PeerEcho`.
    pub peer_probes_answered: u64,
    /// Valid `PeerEcho` datagrams received from configured peers.
    pub peer_echoes_received: u64,
    /// `PeerRelay` datagrams transmitted to configured peers.
    pub peer_relays_sent: u64,
    /// Valid `PeerRelay` datagrams received from configured peers.
    pub peer_relays_received: u64,
}

impl NetworkCounts {
    fn record_transient(&mut self, restricted: bool) {
        self.unsent += 1;
        if restricted {
            self.blocked += 1;
        }
    }
}

/// Encodes a TX departure tag for a `PeerProbe` to `peer_idx` with `sequence`.
fn peer_probe_tag(peer_idx: usize, sequence: u64) -> u64 {
    PEER_PROBE_TAG_BIT
        | (((peer_idx as u64) & PEER_IDX_MASK) << PEER_IDX_SHIFT)
        | (sequence & PEER_SEQ_MASK)
}

/// Pure receiver network state machine: validates audio/control datagrams,
/// drives retransmission requests, runs [`Sync`] (peer probes, peer echoes,
/// link-state relays, BLUE + modal Kalman snapshots), and enforces the strict
/// `(canonical_addr, identity)` peer allowlist over any [`DatagramSink`].
///
/// Owns no OS sockets and reads no wall/monotonic clocks directly, so both
/// [`ReceiverNetwork`] (over UDP) and deterministic simulators run the exact
/// same production protocol engine.
pub struct ReceiverNetEngine {
    stream: u16,
    sync_identity: u64,
    /// Preallocated buffer for padded outgoing reports and requests.
    outgoing: Box<[u8]>,
    /// Preallocated buffer for outgoing `PeerRelay` broadcasts.
    relay_buf: Box<[u8]>,
    /// Sender of the confirmed timeline of the stream.
    sender: Option<SocketAddr>,
    /// Confirmed timeline associated with `sender`.
    sender_timeline: Option<u64>,
    /// Confirmed sender clock identity associated with `sender`.
    sender_clock_id: Option<u32>,
    /// Length of audio packets on that timeline, to which reports are padded.
    length: usize,
    /// Candidate sender metadata while awaiting audio-thread confirmation.
    pending: Option<PendingSender>,
    /// Missing-frame retransmission tracker for the active timeline.
    retransmission: RetransmissionTracker,
    /// Unified peer/star sync engine (`Some` in `SyncMode::Peer`, `None` in
    /// `SyncMode::Hull`). Boxed once at construction to keep stack frames small.
    sync: Option<Box<Sync>>,
    /// Configured direct peers, indexed identically to `Sync`'s peer slots.
    peers: Box<[AllowedPeer]>,
    /// Relay interval used for backoff when all incident edges are stale.
    relay_interval_ns: i64,
    /// Backoff deadline preventing busy-spin when `build_relay` returns `None`.
    relay_backoff_until: Option<i64>,
    /// Periodic wake interval for expiring silent peers when `peer_active`.
    stale_check_interval_ns: i64,
    /// Next periodic stale-peer check deadline while `peer_active`.
    next_stale_check_ns: Option<i64>,
    /// Latest `(clock_id, SyncSnapshot)` queued for delivery to the audio end.
    pending_snapshot: Option<(u32, SyncSnapshot)>,
    /// Last `(clock_id, SyncSnapshot)` handed to the audio end, to suppress
    /// duplicate publications.
    last_published_snapshot: Option<(u32, SyncSnapshot)>,
    counts: NetworkCounts,
}

impl ReceiverNetEngine {
    /// Creates a pure receiver network engine from `config`, preallocating all
    /// packet, relay, and sync state once.
    #[must_use]
    pub fn new(config: &NetConfig) -> ReceiverNetEngine {
        let mut allowed_peers = Vec::new();
        let sync = match config.sync_mode {
            SyncMode::Hull => None,
            SyncMode::Peer => {
                let mut sync = Box::new(Sync::new(config.sync_settings));
                sync.set_sender_weight_q16(config.sender_weight_q16);
                for peer in &config.peers {
                    if let Some(slot) = sync.add_peer(peer.identity, peer.weight_q16) {
                        debug_assert_eq!(slot, allowed_peers.len());
                        allowed_peers.push(AllowedPeer {
                            identity: peer.identity,
                            address: peer.address,
                            canonical: canonical_addr(peer.address),
                        });
                    }
                }
                Some(sync)
            }
        };
        let relay_interval_ns = if config.sync_settings.relay_interval_ns > 0 {
            config.sync_settings.relay_interval_ns
        } else {
            DEFAULT_RELAY_INTERVAL_NS
        };
        let stale_check_interval_ns =
            (config.sync_settings.peer_stale_ns / 4).clamp(100_000_000, 1_000_000_000);
        ReceiverNetEngine {
            stream: config.stream,
            sync_identity: config.sync_settings.identity,
            outgoing: vec![0u8; config.datagram.max(packet::REPORT + packet::NEEDS)]
                .into_boxed_slice(),
            relay_buf: vec![0u8; packet::PEER_RELAY_MAX].into_boxed_slice(),
            sender: None,
            sender_timeline: None,
            sender_clock_id: None,
            length: 0,
            pending: None,
            retransmission: RetransmissionTracker::new(),
            sync,
            peers: allowed_peers.into_boxed_slice(),
            relay_interval_ns,
            relay_backoff_until: None,
            stale_check_interval_ns,
            next_stale_check_ns: None,
            pending_snapshot: None,
            last_published_snapshot: None,
            counts: NetworkCounts::default(),
        }
    }

    /// Cumulative network counters.
    #[must_use]
    pub fn counts(&self) -> NetworkCounts {
        self.counts
    }

    /// Latest [`SyncSnapshot`] from [`Sync`], or `None` in legacy hull mode.
    #[must_use]
    pub fn sync_snapshot(&self) -> Option<SyncSnapshot> {
        self.sync.as_ref().map(|sync| sync.snapshot())
    }

    /// Whether a new `(clock_id, SyncSnapshot)` is waiting to be taken.
    #[must_use]
    pub fn has_pending_sync_update(&self) -> bool {
        self.pending_snapshot.is_some()
    }

    /// Takes the newest pending `(clock_id, SyncSnapshot)` update, if any.
    pub fn take_sync_update(&mut self) -> Option<(u32, SyncSnapshot)> {
        self.pending_snapshot.take()
    }

    /// Clears the last-published snapshot cache so the next [`Self::step`]
    /// republishes if the audio ring dropped a `SyncUpdate`.
    pub fn mark_snapshot_dropped(&mut self) {
        self.last_published_snapshot = None;
    }

    /// Confirmed sender address, if any.
    #[must_use]
    pub fn sender(&self) -> Option<SocketAddr> {
        self.sender
    }

    /// Confirmed sender timeline, if any.
    #[must_use]
    pub fn sender_timeline(&self) -> Option<u64> {
        self.sender_timeline
    }

    /// Confirmed sender clock identity, if any.
    #[must_use]
    pub fn sender_clock_id(&self) -> Option<u32> {
        self.sender_clock_id
    }

    /// Updates the confirmed sender clock identity, resetting sender-side sync
    /// state (while preserving direct peer links) if the sender rebooted, and
    /// updating `Sync`'s `sender_clock_id` so incoming `PeerRelay` sender edges
    /// are fenced to the active sender clock.
    fn update_sender_clock_id(&mut self, clock_id: u32) {
        if self.sender_clock_id == Some(clock_id) {
            return;
        }
        let rebooted = self.sender_clock_id.is_some();
        self.sender_clock_id = Some(clock_id);
        if let Some(sync) = self.sync.as_mut() {
            if rebooted {
                sync.reset_sender_clock();
            }
            sync.set_sender_clock_id(clock_id);
        }
        if rebooted {
            self.relay_backoff_until = None;
            self.pending_snapshot = None;
            self.last_published_snapshot = None;
        }
    }

    /// Promotes any cached candidate sender once the audio consumer confirms
    /// its timeline, and resets sender sync state if `clock_id` changed.
    pub fn sync_confirmed(&mut self, confirmed: ConfirmedState) {
        if !confirmed.active {
            return;
        }
        self.update_sender_clock_id(confirmed.clock_id);
        if self.sender_timeline == Some(confirmed.timeline) {
            return;
        }
        if let Some(pending) = self.pending
            && pending.timeline == confirmed.timeline
        {
            self.sender = Some(pending.from);
            self.sender_timeline = Some(confirmed.timeline);
            self.length = pending.length;
            self.retransmission = pending.retransmission;
            self.pending = None;
            self.update_sender_clock_id(pending.clock_id);
        }
    }

    /// Checks whether `(from, identity)` matches a single configured peer entry
    /// (enforcing strict 1-to-1 address-to-identity binding).
    fn match_peer(&self, from: SocketAddr, identity: u64) -> Option<AllowedPeer> {
        let canonical = canonical_addr(from);
        self.peers
            .iter()
            .copied()
            .find(|peer| peer.canonical == canonical && peer.identity == identity)
    }

    /// Advances [`Sync::step`] at `now_ns` and queues a new `SyncUpdate` when
    /// a valid snapshot differs from the last published one.
    fn sync_step_and_queue(&mut self, now_ns: i64) {
        let (Some(sync), Some(clock_id)) = (self.sync.as_mut(), self.sender_clock_id) else {
            return;
        };
        let snap = sync.step(now_ns);
        if snap.valid && self.last_published_snapshot != Some((clock_id, snap)) {
            self.pending_snapshot = Some((clock_id, snap));
            self.last_published_snapshot = Some((clock_id, snap));
        }
    }

    /// Updates `sender`, `length`, and `retransmission` for an accepted audio
    /// packet, gating state changes on audio-thread confirmation when an audio
    /// consumer is attached so stray packets cannot hijack reports or clear
    /// gaps.
    fn record_audio(
        &mut self,
        header: &Audio,
        from: SocketAddr,
        length: usize,
        arrival: i64,
        confirmed: ConfirmedState,
    ) {
        self.sync_confirmed(confirmed);
        if !confirmed.attached {
            self.sender = Some(from);
            self.sender_timeline = Some(header.timeline);
            self.length = length;
            self.retransmission.arrived(header, arrival);
            self.update_sender_clock_id(header.clock);
            return;
        }
        if confirmed.active && header.timeline == confirmed.timeline {
            if self.sender_timeline != Some(confirmed.timeline) {
                self.sender = Some(from);
                self.sender_timeline = Some(confirmed.timeline);
                self.length = length;
                self.retransmission.arrived(header, arrival);
                self.update_sender_clock_id(header.clock);
            } else if self
                .sender
                .is_some_and(|known| canonical_addr(known) == canonical_addr(from))
            {
                self.length = length;
                self.retransmission.arrived(header, arrival);
            }
        } else {
            // Unconfirmed timeline: track arriving packets in `pending`
            // without disturbing the active sender or retransmission tracker.
            match &mut self.pending {
                Some(pending) if pending.timeline == header.timeline => {
                    if canonical_addr(pending.from) == canonical_addr(from) {
                        pending.clock_id = header.clock;
                        pending.length = length;
                        pending.retransmission.arrived(header, arrival);
                    }
                }
                _ => {
                    let mut retransmission = RetransmissionTracker::new();
                    retransmission.arrived(header, arrival);
                    self.pending = Some(PendingSender {
                        timeline: header.timeline,
                        clock_id: header.clock,
                        from,
                        length,
                        retransmission,
                    });
                }
            }
        }
    }

    /// Processes one incoming UDP datagram from `from` stamped with arrival
    /// time `arrival_ns` and local reply time `departure_ns`.
    ///
    /// When `accept_audio` is `false` (for example under audio-ring
    /// backpressure), valid audio packets are dropped without modifying
    /// `retransmission` state while all control and peer-sync datagrams are
    /// still processed normally.
    ///
    /// # Errors
    ///
    /// Returns any fatal transport error from `sink`.
    #[allow(clippy::too_many_arguments)]
    pub fn on_datagram<S: DatagramSink>(
        &mut self,
        from: SocketAddr,
        bytes: &[u8],
        arrival_ns: i64,
        departure_ns: i64,
        confirmed: ConfirmedState,
        accept_audio: bool,
        sink: &mut S,
    ) -> Result<DatagramAction, S::Error> {
        self.sync_confirmed(confirmed);
        match packet::kind(bytes) {
            Ok(KIND_AUDIO) => match parse_audio(bytes) {
                Ok(header) if header.stream == self.stream => {
                    if (confirmed.rate != 0 && header.rate != confirmed.rate)
                        || (confirmed.channels != 0 && header.channels != confirmed.channels)
                    {
                        self.counts.other += 1;
                        return Ok(DatagramAction::Consumed);
                    }
                    if !accept_audio {
                        self.counts.dropped += 1;
                        return Ok(DatagramAction::Consumed);
                    }
                    self.record_audio(&header, from, bytes.len(), arrival_ns, confirmed);
                    Ok(DatagramAction::Audio(header))
                }
                _ => {
                    self.counts.other += 1;
                    Ok(DatagramAction::Consumed)
                }
            },
            Ok(KIND_ECHO) => match parse_echo(bytes) {
                Ok(echo) if echo.stream == self.stream => {
                    if self
                        .sender
                        .is_some_and(|known| canonical_addr(known) != canonical_addr(from))
                    {
                        self.counts.other += 1;
                        return Ok(DatagramAction::Consumed);
                    }
                    if let Some(sync) = self.sync.as_mut() {
                        if self.sender.is_none() || echo.receiver != self.sync_identity {
                            self.counts.other += 1;
                            return Ok(DatagramAction::Consumed);
                        }
                        self.counts.answers += 1;
                        if sync.on_sender_echo(&echo, arrival_ns) {
                            self.relay_backoff_until = None;
                            self.sync_step_and_queue(arrival_ns);
                        }
                        Ok(DatagramAction::Consumed)
                    } else {
                        Ok(DatagramAction::HullEcho(echo))
                    }
                }
                _ => {
                    self.counts.other += 1;
                    Ok(DatagramAction::Consumed)
                }
            },
            Ok(kind @ (KIND_PEER_PROBE | KIND_PEER_ECHO | KIND_PEER_RELAY)) => {
                self.on_peer_datagram(kind, from, bytes, arrival_ns, departure_ns, sink)?;
                Ok(DatagramAction::Consumed)
            }
            _ => {
                self.counts.other += 1;
                Ok(DatagramAction::Consumed)
            }
        }
    }

    /// Processes one peer-sync datagram (`PeerProbe`, `PeerEcho`, or
    /// `PeerRelay`) after enforcing the strict `(canonical_addr, identity)`
    /// peer allowlist.
    fn on_peer_datagram<S: DatagramSink>(
        &mut self,
        kind: u8,
        from: SocketAddr,
        bytes: &[u8],
        arrival_ns: i64,
        departure_ns: i64,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        match kind {
            KIND_PEER_PROBE => {
                let Ok(probe) = parse_peer_probe(bytes) else {
                    self.counts.other += 1;
                    return Ok(());
                };
                if probe.stream != self.stream
                    || self.match_peer(from, probe.prober).is_none()
                    || self.sync.is_none()
                {
                    self.counts.other += 1;
                    return Ok(());
                }
                let reply_departure = departure_ns.max(arrival_ns);
                let answer = self
                    .sync
                    .as_ref()
                    .and_then(|sync| sync.on_peer_probe(&probe, arrival_ns, reply_departure));
                let Some(peer_echo) = answer else {
                    self.counts.other += 1;
                    return Ok(());
                };
                let mut out = [0u8; packet::PEER_ECHO];
                if let Some(len) = write_peer_echo(&peer_echo, &mut out) {
                    match sink.send(from, &out[..len], None)? {
                        SendStatus::Sent => self.counts.peer_probes_answered += 1,
                        SendStatus::Transient { restricted } => {
                            self.counts.record_transient(restricted);
                        }
                    }
                }
            }
            KIND_PEER_ECHO => {
                let Ok(echo) = parse_peer_echo(bytes) else {
                    self.counts.other += 1;
                    return Ok(());
                };
                if echo.stream != self.stream
                    || self.match_peer(from, echo.responder).is_none()
                    || self.sync.is_none()
                {
                    self.counts.other += 1;
                    return Ok(());
                }
                self.counts.peer_echoes_received += 1;
                let accepted = self
                    .sync
                    .as_mut()
                    .is_some_and(|sync| sync.on_peer_echo(&echo, arrival_ns));
                if accepted {
                    self.relay_backoff_until = None;
                    self.sync_step_and_queue(arrival_ns);
                }
            }
            KIND_PEER_RELAY => {
                let Ok(relay) = parse_peer_relay(bytes) else {
                    self.counts.other += 1;
                    return Ok(());
                };
                if relay.stream != self.stream
                    || self.match_peer(from, relay.sender).is_none()
                    || self.sync.is_none()
                {
                    self.counts.other += 1;
                    return Ok(());
                }
                self.counts.peer_relays_received += 1;
                let accepted = self
                    .sync
                    .as_mut()
                    .map_or(0, |sync| sync.on_peer_relay(&relay, arrival_ns));
                if accepted > 0 {
                    self.sync_step_and_queue(arrival_ns);
                }
            }
            _ => self.counts.other += 1,
        }
        Ok(())
    }

    /// Processes one TX departure timestamp.
    ///
    /// - Bit 63 set (`PeerProbe`): feeds `Sync::peer_probe_departed` and
    ///   returns `None`.
    /// - Bit 63 clear (`Report`): feeds `Sync::report_departed` in `Peer` mode
    ///   and returns `None`, or returns `Some((sequence, time_ns))` for
    ///   forwarding as `Incoming::Departed` in legacy `Hull` mode.
    pub fn on_departure(&mut self, tag: u64, time_ns: i64) -> Option<(u64, i64)> {
        if (tag & PEER_PROBE_TAG_BIT) != 0 {
            if let Some(sync) = self.sync.as_mut() {
                let peer_idx = ((tag >> PEER_IDX_SHIFT) & PEER_IDX_MASK) as usize;
                let sequence = tag & PEER_SEQ_MASK;
                sync.peer_probe_departed(peer_idx, sequence, time_ns);
            }
            return None;
        }
        if let Some(sync) = self.sync.as_mut() {
            sync.report_departed(tag, time_ns);
            None
        } else {
            Some((tag, time_ns))
        }
    }

    /// Sends one report and its recent needs to the confirmed sender, padded
    /// to at least the space required for needs and the length of audio
    /// packets on the active timeline.
    ///
    /// # Errors
    ///
    /// Returns any fatal transport error from `sink`.
    pub fn send_report<S: DatagramSink>(
        &mut self,
        outgoing: &Outgoing,
        sink: &mut S,
    ) -> Result<(), S::Error> {
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
        let tag = report.sequence & !PEER_PROBE_TAG_BIT;
        match sink.send(to, bytes, Some(tag))? {
            SendStatus::Sent => self.counts.reports += 1,
            SendStatus::Transient { restricted } => self.counts.record_transient(restricted),
        }
        Ok(())
    }

    /// Runs periodic network duties at `now_ns`: sends due retransmission
    /// requests, transmits due `PeerProbe`s and `PeerRelay`s, and advances
    /// [`Sync::step`] (expiring stale peers and queuing any updated snapshot).
    ///
    /// # Errors
    ///
    /// Returns any fatal transport error from `sink`.
    pub fn step<S: DatagramSink>(
        &mut self,
        now_ns: i64,
        confirmed: ConfirmedState,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        self.sync_confirmed(confirmed);
        self.send_retransmit_requests(now_ns, sink)?;
        if self.sync.is_some() {
            self.send_due_peer_probes(now_ns, sink)?;
            self.send_due_peer_relay(now_ns, sink)?;
            self.sync_step_and_queue(now_ns);
            let peer_active = self
                .sync
                .as_ref()
                .is_some_and(|sync| sync.snapshot().peer_active);
            if peer_active {
                if self
                    .next_stale_check_ns
                    .is_none_or(|deadline| now_ns >= deadline)
                {
                    self.next_stale_check_ns =
                        Some(now_ns.saturating_add(self.stale_check_interval_ns));
                }
            } else {
                self.next_stale_check_ns = None;
            }
        }
        Ok(())
    }

    /// Earliest local-clock timestamp at which [`Self::step`] has timed work
    /// (retransmission retry, peer probe, peer relay, or stale-peer check).
    ///
    /// Never returns `<= now_ns` in a busy-spin loop when no work is actually
    /// executable.
    #[must_use]
    pub fn next_wake_ns(&self, now_ns: i64) -> Option<i64> {
        let mut earliest: Option<i64> = None;
        let mut consider = |at: i64| {
            earliest = match earliest {
                Some(prev) if prev <= at => Some(prev),
                _ => Some(at),
            };
        };
        if self.sender.is_some()
            && let Some(due_in) = self.retransmission.next_due(now_ns)
        {
            consider(now_ns.saturating_add(due_in.max(0)));
        }
        if let Some(sync) = self.sync.as_ref()
            && sync.peer_count() > 0
        {
            if let Some(at) = sync.next_peer_probe_at(now_ns) {
                consider(at);
            }
            if sync.should_relay(now_ns) {
                let at = match self.relay_backoff_until {
                    Some(until) if until > now_ns => until,
                    _ => now_ns,
                };
                consider(at);
            } else if let Some(at) = sync.next_relay_at(now_ns)
                && at > now_ns
            {
                let target = self.relay_backoff_until.map_or(at, |until| at.max(until));
                consider(target);
            }
            if let Some(at) = self.next_stale_check_ns {
                consider(at);
            }
        }
        earliest
    }

    /// Sends all due retransmission requests to the active sender.
    fn send_retransmit_requests<S: DatagramSink>(
        &mut self,
        now_ns: i64,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        let Some(to) = self.sender else {
            return Ok(());
        };
        while let Some(req) = self.retransmission.due(now_ns) {
            let request = Request {
                stream: self.stream,
                timeline: req.timeline,
                first: req.first,
                frames: req.frames,
            };
            let Some(length) = write_request(&request, &mut self.outgoing) else {
                break;
            };
            let bytes = self.outgoing.get(..length).unwrap_or(&[]);
            match sink.send(to, bytes, None)? {
                SendStatus::Sent => self.counts.requests += 1,
                SendStatus::Transient { restricted } => {
                    self.counts.record_transient(restricted);
                    break;
                }
            }
        }
        Ok(())
    }

    /// Emits all due `PeerProbe` datagrams at `now_ns`.
    fn send_due_peer_probes<S: DatagramSink>(
        &mut self,
        now_ns: i64,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        let mut out = [0u8; packet::PEER_PROBE];
        loop {
            let next = self
                .sync
                .as_mut()
                .and_then(|sync| sync.next_peer_probe(now_ns));
            let Some((peer_idx, probe)) = next else {
                break;
            };
            let Some(peer) = self.peers.get(peer_idx).copied() else {
                continue;
            };
            let Some(len) = write_peer_probe(&probe, &mut out) else {
                continue;
            };
            let tag = peer_probe_tag(peer_idx, probe.sequence);
            match sink.send(peer.address, &out[..len], Some(tag))? {
                SendStatus::Sent => self.counts.peer_probes_sent += 1,
                SendStatus::Transient { restricted } => self.counts.record_transient(restricted),
            }
        }
        Ok(())
    }

    /// Broadcasts a `PeerRelay` to all configured peers when due at `now_ns`.
    fn send_due_peer_relay<S: DatagramSink>(
        &mut self,
        now_ns: i64,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        let due = self
            .sync
            .as_ref()
            .is_some_and(|sync| sync.should_relay(now_ns))
            && self.relay_backoff_until.is_none_or(|until| now_ns >= until);
        if !due {
            return Ok(());
        }
        let relay = self.sync.as_mut().and_then(|sync| sync.build_relay(now_ns));
        let Some(relay) = relay else {
            // All incident edges are stale; back off one relay interval rather
            // than spinning at 0 ms poll timeout.
            self.relay_backoff_until = Some(now_ns.saturating_add(self.relay_interval_ns));
            return Ok(());
        };
        self.relay_backoff_until = None;
        let Some(len) = write_peer_relay(&relay, &mut self.relay_buf) else {
            return Ok(());
        };
        let bytes = self.relay_buf.get(..len).unwrap_or(&[]);
        for peer in &self.peers {
            match sink.send(peer.address, bytes, None)? {
                SendStatus::Sent => self.counts.peer_relays_sent += 1,
                SendStatus::Transient { restricted } => self.counts.record_transient(restricted),
            }
        }
        Ok(())
    }
}

/// Socket-independent bridge binding [`NetworkEnd`] SPSC rings and
/// [`ReceiverNetEngine`] together.
///
/// Shared directly by [`ReceiverNetwork`] (over a real UDP socket) and
/// deterministic simulators so both exercise the exact ring capacities,
/// buffer-recycling backpressure, atomic confirmation handshake, report
/// draining, and `SyncSnapshot` handoff.
pub struct ReceiverNetBridge {
    end: NetworkEnd,
    engine: ReceiverNetEngine,
}

impl ReceiverNetBridge {
    /// Creates a bridge pairing `end` with a [`ReceiverNetEngine`] configured
    /// by `config`.
    #[must_use]
    pub fn new(end: NetworkEnd, config: &NetConfig) -> ReceiverNetBridge {
        ReceiverNetBridge {
            end,
            engine: ReceiverNetEngine::new(config),
        }
    }

    /// Returns cumulative network counters.
    #[must_use]
    pub fn counts(&self) -> NetworkCounts {
        self.engine.counts()
    }

    /// Latest [`SyncSnapshot`] from [`Sync`], or `None` in legacy hull mode.
    #[must_use]
    pub fn sync_snapshot(&self) -> Option<SyncSnapshot> {
        self.engine.sync_snapshot()
    }

    /// Underlying pure receiver network engine.
    #[must_use]
    pub fn engine(&self) -> &ReceiverNetEngine {
        &self.engine
    }

    /// Earliest local-clock timestamp at which this bridge needs another
    /// [`Self::step`], returning `Some(now_ns)` immediately when outgoing
    /// reports or a pending `SyncSnapshot` wait to be flushed.
    #[must_use]
    pub fn next_wake_ns(&self, now_ns: i64) -> Option<i64> {
        if self.end.reports.waiting() > 0 || self.engine.has_pending_sync_update() {
            return Some(now_ns);
        }
        self.engine.next_wake_ns(now_ns)
    }

    /// Synchronizes audio-thread confirmation state into the network engine.
    fn sync_confirmed(&mut self) -> ConfirmedState {
        let confirmed = self.end.confirmed.load();
        self.engine.sync_confirmed(confirmed);
        confirmed
    }

    /// Pushes any queued [`SyncSnapshot`] update into the audio ring, marking
    /// it for retry if the ring is momentarily full.
    fn flush_sync_update(&mut self) {
        if let Some((clock_id, snapshot)) = self.engine.take_sync_update()
            && self
                .end
                .incoming
                .put(Incoming::SyncUpdate { clock_id, snapshot })
                .is_err()
        {
            self.engine.counts.dropped += 1;
            self.engine.mark_snapshot_dropped();
        }
    }

    /// Delivers one TX departure timestamp into the engine (and forwards it to
    /// the audio ring in legacy hull mode).
    pub fn deliver_departure(&mut self, tag: u64, time_ns: i64) {
        if let Some((sequence, time)) = self.engine.on_departure(tag, time_ns)
            && self
                .end
                .incoming
                .put(Incoming::Departed { sequence, time })
                .is_err()
        {
            self.engine.counts.dropped += 1;
        }
    }

    /// Drains all outgoing reports queued by [`ReceiverAudio`] and sends them
    /// through `sink`.
    ///
    /// # Errors
    ///
    /// Returns any fatal transport error from `sink`.
    pub fn flush_reports<S: DatagramSink>(&mut self, sink: &mut S) -> Result<(), S::Error> {
        self.sync_confirmed();
        while let Some(outgoing) = self.end.reports.take() {
            self.engine.send_report(&outgoing, sink)?;
        }
        Ok(())
    }

    /// Runs periodic network duties at `now_ns`, flushing queued audio-thread
    /// reports, running peer probes/relays/retransmissions, and pushing any
    /// updated [`SyncSnapshot`] into the audio ring.
    ///
    /// # Errors
    ///
    /// Returns any fatal transport error from `sink`.
    pub fn step<S: DatagramSink>(&mut self, now_ns: i64, sink: &mut S) -> Result<(), S::Error> {
        let confirmed = self.sync_confirmed();
        while let Some(outgoing) = self.end.reports.take() {
            self.engine.send_report(&outgoing, sink)?;
        }
        self.engine.step(now_ns, confirmed, sink)?;
        self.flush_sync_update();
        Ok(())
    }

    /// Delivers one incoming datagram buffer slice into the bridge using the
    /// exact spare-buffer recycling and overflow backpressure of
    /// [`ReceiverNetwork`].
    ///
    /// # Errors
    ///
    /// Returns any fatal transport error from `sink`.
    pub fn deliver_datagram<S: DatagramSink>(
        &mut self,
        from: SocketAddr,
        bytes: &[u8],
        arrival_ns: i64,
        departure_ns: i64,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        if self.end.kept.is_none() {
            self.end.kept = self.end.spare.take();
        }
        let confirmed = self.end.confirmed.load();
        if let Some(buffer) = self.end.kept.as_mut()
            && bytes.len() <= buffer.len()
        {
            buffer[..bytes.len()].copy_from_slice(bytes);
            self.handle_kept_datagram(
                from,
                bytes.len(),
                arrival_ns,
                departure_ns,
                confirmed,
                sink,
            )?;
        } else {
            self.handle_overflow_datagram(from, bytes, arrival_ns, departure_ns, confirmed, sink)?;
        }
        self.flush_sync_update();
        Ok(())
    }

    /// Processes a datagram already written into `self.end.kept[..length]`.
    fn handle_kept_datagram<S: DatagramSink>(
        &mut self,
        from: SocketAddr,
        length: usize,
        arrival_ns: i64,
        departure_ns: i64,
        confirmed: ConfirmedState,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        let action = {
            let Some(buffer) = self.end.kept.as_ref() else {
                return Ok(());
            };
            let bytes = buffer.get(..length).unwrap_or(&[]);
            self.engine
                .on_datagram(from, bytes, arrival_ns, departure_ns, confirmed, true, sink)?
        };
        match action {
            DatagramAction::Consumed => {}
            DatagramAction::Audio(header) => {
                if let Some(buffer) = self.end.kept.take() {
                    let item = Incoming::Packet {
                        buffer,
                        header,
                        length,
                        arrival: arrival_ns,
                    };
                    match self.end.incoming.put(item) {
                        Ok(()) => self.engine.counts.packets += 1,
                        Err(Incoming::Packet { buffer, .. }) => {
                            self.end.kept = Some(buffer);
                            self.engine.counts.dropped += 1;
                        }
                        Err(_) => self.engine.counts.dropped += 1,
                    }
                }
            }
            DatagramAction::HullEcho(echo) => {
                if self.end.incoming.put(Incoming::Answer(echo)).is_err() {
                    self.engine.counts.dropped += 1;
                } else {
                    self.engine.counts.answers += 1;
                }
            }
        }
        Ok(())
    }

    /// Processes a datagram when no audio buffer is spare (control packets are
    /// handled normally while audio packets are dropped under backpressure).
    fn handle_overflow_datagram<S: DatagramSink>(
        &mut self,
        from: SocketAddr,
        bytes: &[u8],
        arrival_ns: i64,
        departure_ns: i64,
        confirmed: ConfirmedState,
        sink: &mut S,
    ) -> Result<(), S::Error> {
        let action = self.engine.on_datagram(
            from,
            bytes,
            arrival_ns,
            departure_ns,
            confirmed,
            false,
            sink,
        )?;
        if let DatagramAction::HullEcho(echo) = action {
            if self.end.incoming.put(Incoming::Answer(echo)).is_err() {
                self.engine.counts.dropped += 1;
            } else {
                self.engine.counts.answers += 1;
            }
        }
        Ok(())
    }
}

/// The network thread of a receiver: thin UDP shell around
/// [`ReceiverNetBridge`].
pub struct ReceiverNetwork {
    socket: Socket,
    bridge: ReceiverNetBridge,
    /// Where datagrams go when no audio buffer is spare (control packets are
    /// still parsed and handled out of this buffer; audio packets are dropped).
    overflow: Box<[u8]>,
}

impl ReceiverNetwork {
    /// Creates a legacy lower-hull receiver network worker for `stream` bound
    /// to `socket` and paired with `end`.
    ///
    /// Use [`ReceiverNetwork::with_config`] to enable unified peer/star
    /// synchronization ([`SyncMode::Peer`]).
    #[must_use]
    pub fn new(socket: Socket, end: NetworkEnd, stream: u16, sizes: Sizes) -> ReceiverNetwork {
        ReceiverNetwork::with_config(socket, end, &NetConfig::hull(stream, sizes.datagram))
    }

    /// Creates a receiver network worker configured by `config`.
    #[must_use]
    pub fn with_config(socket: Socket, end: NetworkEnd, config: &NetConfig) -> ReceiverNetwork {
        let datagram = config.datagram;
        ReceiverNetwork {
            socket,
            bridge: ReceiverNetBridge::new(end, config),
            overflow: vec![0u8; datagram].into_boxed_slice(),
        }
    }

    /// Returns cumulative network counters.
    #[must_use]
    pub fn counts(&self) -> NetworkCounts {
        self.bridge.counts()
    }

    /// Returns a reference to the underlying UDP socket.
    #[must_use]
    pub fn socket(&self) -> &Socket {
        &self.socket
    }

    /// Latest [`SyncSnapshot`] from [`Sync`], or `None` in legacy hull mode.
    #[must_use]
    pub fn sync_snapshot(&self) -> Option<SyncSnapshot> {
        self.bridge.sync_snapshot()
    }

    /// Underlying pure receiver network engine.
    #[must_use]
    pub fn engine(&self) -> &ReceiverNetEngine {
        self.bridge.engine()
    }

    /// Computes how long `socket.wait` should sleep, returning early if
    /// outgoing reports, a pending sync update, or any engine timer is due
    /// sooner than `milliseconds`.
    fn wait_timeout(&self, milliseconds: i32) -> i32 {
        let now = clock::raw();
        if let Some(wake_ns) = self.bridge.next_wake_ns(now) {
            let remaining_ns = wake_ns.saturating_sub(now).max(0);
            let wait_ms =
                i32::try_from(remaining_ns.saturating_add(999_999) / 1_000_000).unwrap_or(i32::MAX);
            return if milliseconds < 0 {
                wait_ms
            } else {
                milliseconds.min(wait_ms)
            };
        }
        milliseconds
    }

    /// Drains all available TX departure timestamps from the socket into the
    /// bridge.
    fn drain_departures(&mut self) -> io::Result<()> {
        while let Some(departure) = self.socket.departure()? {
            self.bridge
                .deliver_departure(departure.tag, departure.stamp.time);
        }
        Ok(())
    }

    /// Runs one network loop iteration: polls the socket up to `milliseconds`,
    /// drains TX departure timestamps before incoming datagrams (so every
    /// `t1` is recorded before its `Echo` or `PeerEcho` is matched), transmits
    /// queued reports, runs peer probing/relaying and retransmission timers,
    /// and publishes any updated [`SyncSnapshot`].
    ///
    /// # Errors
    ///
    /// Returns a fatal socket I/O error.
    pub fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        self.bridge.sync_confirmed();
        let wait_ms = self.wait_timeout(milliseconds);
        self.socket.wait(wait_ms)?;
        // Drain departures BEFORE incoming datagrams so `t1` for a sent
        // Report or PeerProbe is always recorded before its Echo/PeerEcho.
        self.drain_departures()?;
        for _ in 0..MAX_RECEIVE_PER_TURN {
            if !self.receive()? {
                break;
            }
        }
        self.bridge
            .step(clock::raw(), &mut SocketSink(&mut self.socket))?;
        self.drain_departures()?;
        self.bridge.flush_sync_update();
        Ok(())
    }

    /// Takes in one datagram, if one is waiting, and says whether one was.
    fn receive(&mut self) -> io::Result<bool> {
        if self.bridge.end.kept.is_none() {
            self.bridge.end.kept = self.bridge.end.spare.take();
        }
        let confirmed = self.bridge.end.confirmed.load();
        if let Some(buffer) = self.bridge.end.kept.as_mut() {
            let Some(received) = self.socket.receive(buffer)? else {
                return Ok(false);
            };
            self.bridge.handle_kept_datagram(
                received.from,
                received.length,
                received.arrival.time,
                clock::raw(),
                confirmed,
                &mut SocketSink(&mut self.socket),
            )?;
            return Ok(true);
        }
        // No audio buffer is spare: still receive into `overflow` so control
        // and peer-sync datagrams are processed normally while audio packets
        // are cleanly dropped.
        let Some(received) = self.socket.receive(&mut self.overflow)? else {
            return Ok(false);
        };
        let bytes = self.overflow.get(..received.length).unwrap_or(&[]);
        self.bridge.handle_overflow_datagram(
            received.from,
            bytes,
            received.arrival.time,
            clock::raw(),
            confirmed,
            &mut SocketSink(&mut self.socket),
        )?;
        Ok(true)
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

/// Pure report-cadence timer shared between [`ReceiverAudio`] and
/// deterministic simulators.
#[derive(Clone, Copy, Debug, Default)]
pub struct ReportSchedule {
    /// `(first_report_time_ns, next_due_ns)` on the receiver raw clock.
    state: Option<(i64, i64)>,
}

impl ReportSchedule {
    /// Creates an empty schedule whose first report is immediately due.
    #[must_use]
    pub fn new() -> ReportSchedule {
        ReportSchedule { state: None }
    }

    /// Resets the schedule so fast startup reporting restarts (for example on
    /// adopting a new sender timeline).
    pub fn reset(&mut self) {
        self.state = None;
    }

    /// Whether a report is due at local clock `time`. Automatically recovers
    /// if device timestamps jump backwards or place the next due time
    /// impossibly far ahead.
    pub fn due(&mut self, reporting: Reporting, time: i64) -> bool {
        let max_period = reporting.at_start.max(0).max(reporting.after.max(0));
        if let Some((first, due)) = self.state {
            let jumped = time < first || due.saturating_sub(time) > max_period;
            if jumped {
                self.state = None;
            } else if time < due {
                return false;
            }
        }
        true
    }

    /// Records that a report was emitted at local clock `time` and advances
    /// the next due deadline.
    pub fn record_sent(&mut self, reporting: Reporting, time: i64) {
        let at_start = reporting.at_start.max(0);
        let after = reporting.after.max(0);
        let first = self.state.map_or(time, |(first, _)| first);
        let period = if time.saturating_sub(first) < reporting.start.max(0) {
            at_start
        } else {
            after
        };
        self.state = Some((first, time.saturating_add(period)));
    }
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
    report_schedule: ReportSchedule,
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
            report_schedule: ReportSchedule::new(),
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
                            .clock_id
                            .store(header.clock, Ordering::Release);
                        self.end
                            .confirmed
                            .timeline
                            .store(header.timeline, Ordering::Release);
                        self.end.confirmed.active.store(true, Ordering::Release);
                        if heard.adopted {
                            self.report_schedule.reset();
                        }
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
                Incoming::SyncUpdate { clock_id, snapshot } => {
                    if self.playback.receiver().clock_id() == Some(clock_id) {
                        self.playback.apply_sync(snapshot);
                    }
                }
            }
        }
    }

    /// Makes a report when one is due at `time`.
    fn report(&mut self, time: i64) {
        let Some(reporting) = self.intake.reports else {
            return;
        };
        if !self.report_schedule.due(reporting, time) {
            return;
        }
        let Some(report) = self.playback.report() else {
            return;
        };
        let outgoing = Outgoing {
            report,
            needs: self.playback.recent(),
        };
        self.report_schedule.record_sent(reporting, time);
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
    use std::convert::Infallible;
    use std::net::{SocketAddr, UdpSocket};
    use std::time::Duration;

    use unisono_core::packet::{
        self, Audio, Echo, Format, PROTECTION_ON_REQUEST, PeerProbe, PeerRelay, Recent, RelayEdge,
        Report, parse_needs, parse_peer_echo, parse_peer_probe, parse_peer_relay, parse_report,
        write_audio, write_echo, write_peer_echo, write_peer_probe, write_peer_relay,
    };
    use unisono_core::player::{ModalRegulation, Regulation};
    use unisono_core::sync::{SyncSnapshot, WEIGHT_UNITY_Q16};
    use unisono_dsp::Parameters;

    use super::{
        ConfirmedState, DatagramAction, Incoming, Intake, NetConfig, Outgoing, PeerConfig,
        ReceiverAudio, ReceiverNetEngine, ReceiverNetwork, Reporting, Sizes, SyncMode, link,
        peer_probe_tag,
    };
    use crate::audio::Playback;
    use crate::pump::{ReceiverPlayback, Settings};
    use crate::socket::{DatagramSink, SendStatus, Socket};

    struct RecordingSink(Vec<(SocketAddr, Vec<u8>, Option<u64>)>);

    impl RecordingSink {
        fn new() -> Self {
            Self(Vec::new())
        }
    }

    impl DatagramSink for RecordingSink {
        type Error = Infallible;

        fn send(
            &mut self,
            to: SocketAddr,
            bytes: &[u8],
            tag: Option<u64>,
        ) -> Result<SendStatus, Self::Error> {
            self.0.push((to, bytes.to_vec(), tag));
            Ok(SendStatus::Sent)
        }
    }

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
            modal_regulation: None,
            concealment: Parameters::for_rate(48_000),
            block: 256,
            device_range: 10_000_000,
        }
    }

    fn audio_packet(stream: u16, timeline: u64, index: u64, rate: u32, frames: u16) -> Vec<u8> {
        audio_packet_with_clock(stream, timeline, index, rate, frames, 1)
    }

    fn audio_packet_with_clock(
        stream: u16,
        timeline: u64,
        index: u64,
        rate: u32,
        frames: u16,
        clock: u32,
    ) -> Vec<u8> {
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
            clock,
        };
        let payload = usize::from(frames) * 2 * 3;
        let mut buf = vec![0u8; packet::HEADER + payload];
        let len = write_audio(&header, &mut buf).expect("write audio");
        buf.truncate(len);
        buf
    }

    #[test]
    fn net_config_validation_rejects_bad_peers_and_hull_peers() {
        let a: SocketAddr = "127.0.0.1:5001".parse().expect("addr");
        let b: SocketAddr = "127.0.0.1:5002".parse().expect("addr");

        let mut hull = NetConfig::hull(3, 2_048);
        assert!(hull.validate().is_ok());
        hull.peers.push(PeerConfig {
            identity: 2,
            address: a,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        assert!(hull.validate().is_err());

        let mut peer = NetConfig::peer(3, 1, 2_048);
        assert!(peer.validate().is_ok());
        // Self identity rejected.
        peer.peers.push(PeerConfig {
            identity: 1,
            address: a,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        assert!(peer.validate().is_err());

        // Duplicate address with different identity rejected.
        peer.peers.clear();
        peer.peers.push(PeerConfig {
            identity: 2,
            address: a,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        peer.peers.push(PeerConfig {
            identity: 3,
            address: a,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        assert!(peer.validate().is_err());

        // Distinct identity and address accepted.
        peer.peers[1].address = b;
        assert!(peer.validate().is_ok());

        // Duplicate identity with different address rejected.
        peer.peers[1].identity = 2;
        assert!(peer.validate().is_err());
    }

    #[test]
    fn peer_allowlist_enforces_strict_address_identity_binding_and_clamps_t3_t2() {
        let peer_a: SocketAddr = "127.0.0.1:6001".parse().expect("addr");
        let peer_b: SocketAddr = "127.0.0.1:6002".parse().expect("addr");
        let stranger: SocketAddr = "127.0.0.1:6999".parse().expect("addr");

        let mut cfg = NetConfig::peer(3, 1, 2_048);
        cfg.peers.push(PeerConfig {
            identity: 2,
            address: peer_a,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        cfg.peers.push(PeerConfig {
            identity: 3,
            address: peer_b,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        assert!(cfg.validate().is_ok());

        let mut engine = ReceiverNetEngine::new(&cfg);
        let mut sink = RecordingSink::new();
        let mut buf = [0u8; packet::PEER_PROBE];

        // 1. Unknown source address claiming peer A's identity -> rejected.
        let probe_a = PeerProbe {
            stream: 3,
            prober: 2,
            target: 1,
            sequence: 10,
        };
        let len = write_peer_probe(&probe_a, &mut buf).expect("probe");
        let Ok(action) = engine.on_datagram(
            stranger,
            &buf[..len],
            1_000,
            1_100,
            ConfirmedState::UNATTACHED,
            true,
            &mut sink,
        );
        assert_eq!(action, DatagramAction::Consumed);
        assert_eq!(sink.0.len(), 0);
        assert_eq!(engine.counts().other, 1);

        // 2. Peer B spoofing peer A's identity -> rejected.
        let Ok(_) = engine.on_datagram(
            peer_b,
            &buf[..len],
            1_000,
            1_100,
            ConfirmedState::UNATTACHED,
            true,
            &mut sink,
        );
        assert_eq!(sink.0.len(), 0);
        assert_eq!(engine.counts().other, 2);

        // 3. Legitimate peer A with departure < arrival -> answered with clamped t3 == t2.
        let Ok(_) = engine.on_datagram(
            peer_a,
            &buf[..len],
            5_000,
            4_800,
            ConfirmedState::UNATTACHED,
            true,
            &mut sink,
        );
        assert_eq!(sink.0.len(), 1);
        assert_eq!(engine.counts().peer_probes_answered, 1);
        let echo = parse_peer_echo(&sink.0[0].1).expect("peer echo");
        assert_eq!(echo.arrival, 5_000);
        assert_eq!(echo.departure, 5_000);

        // 4. Peer B spoofing peer A on PeerEcho and PeerRelay -> rejected.
        let mut echo_buf = [0u8; packet::PEER_ECHO];
        let pe_len = write_peer_echo(&echo, &mut echo_buf).expect("pe");
        let Ok(_) = engine.on_datagram(
            peer_b,
            &echo_buf[..pe_len],
            6_000,
            6_000,
            ConfirmedState::UNATTACHED,
            true,
            &mut sink,
        );
        assert_eq!(engine.counts().peer_echoes_received, 0);

        let mut relay = PeerRelay::EMPTY;
        relay.stream = 3;
        relay.sender = 2;
        relay.sequence = 1;
        relay.count = 1;
        relay.edges[0] = RelayEdge {
            from_id: 0,
            to_id: 2,
            offset_ns: 100,
            variance_ns2: 25_000_000,
            age_ns: 1_000_000,
        };
        let mut relay_buf = [0u8; packet::PEER_RELAY_MAX];
        let r_len = write_peer_relay(&relay, &mut relay_buf).expect("relay");
        let Ok(_) = engine.on_datagram(
            peer_b,
            &relay_buf[..r_len],
            7_000,
            7_000,
            ConfirmedState::UNATTACHED,
            true,
            &mut sink,
        );
        assert_eq!(engine.counts().peer_relays_received, 0);
    }

    #[test]
    fn peer_probe_tx_tags_and_non_spinning_relay_timer_work() {
        let sender_addr: SocketAddr = "127.0.0.1:7000".parse().expect("addr");
        let peer_addr: SocketAddr = "127.0.0.1:7002".parse().expect("addr");
        let mut cfg = NetConfig::peer(3, 1, 2_048);
        cfg.peers.push(PeerConfig {
            identity: 2,
            address: peer_addr,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        let mut engine = ReceiverNetEngine::new(&cfg);
        let mut sink = RecordingSink::new();

        // First step at t = 1 s emits one PeerProbe with bit-63 tag and does
        // NOT spin on relay before any sender echo arrives.
        let t0 = 1_000_000_000i64;
        let Ok(()) = engine.step(t0, ConfirmedState::UNATTACHED, &mut sink);
        assert_eq!(sink.0.len(), 1);
        let (to, bytes, tag) = &sink.0[0];
        assert_eq!(*to, peer_addr);
        let probe = parse_peer_probe(bytes).expect("probe");
        let expected_tag = peer_probe_tag(0, probe.sequence);
        assert_eq!(*tag, Some(expected_tag));
        // Next wake must be strictly in the future (no 0 ms busy-spin).
        let wake = engine.next_wake_ns(t0).expect("wake scheduled");
        assert!(wake > t0, "next_wake_ns spun: wake={wake}, t0={t0}");

        // Peer probe departure feeds Sync without forwarding to audio thread.
        assert_eq!(engine.on_departure(expected_tag, t0 + 10_000), None);
        // Report departure feeds Sync in Peer mode without forwarding.
        assert_eq!(engine.on_departure(42, t0 + 20_000), None);

        // Accept an audio packet so sender address and clock_id are known.
        let pkt = audio_packet_with_clock(3, 10, 0, 48_000, 240, 77);
        let Ok(DatagramAction::Audio(_)) = engine.on_datagram(
            sender_addr,
            &pkt,
            t0 + 25_000,
            t0 + 25_000,
            ConfirmedState::UNATTACHED,
            true,
            &mut sink,
        ) else {
            panic!("expected audio action");
        };

        // Feed 4 sender Echoes so `sender_min_rtt` calibrates its variance
        // estimator (`len >= 4`, gating `(0, self)` relaying) and queues a
        // valid sync snapshot on the very first echo.
        for i in 0..4u32 {
            let seq = 42 + u64::from(i);
            let dt = i64::from(i) * 40_000;
            if i > 0 {
                assert_eq!(engine.on_departure(seq, t0 + 20_000 + dt), None);
            }
            let echo = Echo {
                stream: 3,
                receiver: 1,
                sequence: seq,
                arrival: t0 + 120_000 + dt,
                departure: t0 + 130_000 + dt,
            };
            let mut echo_buf = [0u8; packet::ECHO];
            let e_len = write_echo(&echo, &mut echo_buf).expect("echo");
            let Ok(DatagramAction::Consumed) = engine.on_datagram(
                sender_addr,
                &echo_buf[..e_len],
                t0 + 230_000 + dt,
                t0 + 230_000 + dt,
                ConfirmedState::UNATTACHED,
                true,
                &mut sink,
            ) else {
                panic!("expected consumed");
            };
            if i == 0 {
                let (cid, snap) = engine.take_sync_update().expect("sync snapshot");
                assert_eq!(cid, 77);
                assert!(snap.valid);
            }
        }

        // Step now emits a calibrated PeerRelay to the peer.
        sink.0.clear();
        let Ok(()) = engine.step(t0 + 400_000, ConfirmedState::UNATTACHED, &mut sink);
        assert_eq!(engine.counts().peer_relays_sent, 1);
        assert_eq!(sink.0.len(), 1);
        let relay = parse_peer_relay(&sink.0[0].1).expect("peer relay");
        assert_eq!(relay.sender, 1);
        assert_eq!(relay.count, 1);

        // Far later (past peer_stale_ns), all edges are stale: `build_relay`
        // returns None, so backoff engages and next_wake_ns stays > now (no spin).
        let stale_t = t0 + 20_000_000_000;
        sink.0.clear();
        let Ok(()) = engine.step(stale_t, ConfirmedState::UNATTACHED, &mut sink);
        let wake_stale = engine.next_wake_ns(stale_t).expect("wake after stale");
        assert!(
            wake_stale > stale_t,
            "stale relay spun: wake={wake_stale}, now={stale_t}"
        );
    }

    #[test]
    fn stale_sync_update_from_old_clock_id_is_fenced_on_audio_thread() {
        let sizes = Sizes {
            buffers: 8,
            datagram: 2_048,
            messages: 16,
        };
        let (mut net_end, audio_end) = link(sizes);
        let mut settings = playback_settings();
        settings.modal_regulation = Some(ModalRegulation::lipsync(1_000_000, 240));
        let playback: ReceiverPlayback<16, 16, 4, 64> = ReceiverPlayback::new(&settings);
        let mut audio = ReceiverAudio::new(
            playback,
            audio_end,
            Intake {
                items: 16,
                reports: Some(Reporting::USUAL),
            },
        );
        let mut out = [0.0f32; 512];

        // Adopt timeline 10 with clock_id = 100.
        assert!(net_end.hand_over(
            &audio_packet_with_clock(3, 10, 0, 48_000, 240, 100),
            1_000_000
        ));
        audio.cycle(&mut out, 0, 1_000_000);
        assert_eq!(audio.playback().receiver().clock_id(), Some(100));

        // Matching clock_id snapshot is applied.
        let mut snap_old = SyncSnapshot::EMPTY;
        snap_old.valid = true;
        snap_old.path_ns = 123_456;
        net_end
            .incoming
            .put(Incoming::SyncUpdate {
                clock_id: 100,
                snapshot: snap_old,
            })
            .ok();
        audio.cycle(&mut out, 256, 6_333_333);
        assert_eq!(audio.playback().receiver().delay(), 123_456);

        // Sender reboots with timeline 11, clock_id = 200 (two consecutive packets).
        assert!(net_end.hand_over(
            &audio_packet_with_clock(3, 11, 0, 48_000, 240, 200),
            12_000_000
        ));
        assert!(net_end.hand_over(
            &audio_packet_with_clock(3, 11, 240, 48_000, 240, 200),
            17_000_000
        ));
        // A stale SyncUpdate from clock_id = 100 arrives after the new packets.
        let mut snap_stale = SyncSnapshot::EMPTY;
        snap_stale.valid = true;
        snap_stale.path_ns = 999_999;
        net_end
            .incoming
            .put(Incoming::SyncUpdate {
                clock_id: 100,
                snapshot: snap_stale,
            })
            .ok();
        audio.cycle(&mut out, 512, 20_000_000);
        assert_eq!(audio.playback().receiver().clock_id(), Some(200));
        // Stale snapshot from clock_id = 100 must NOT overwrite path_ns!
        assert_ne!(audio.playback().receiver().delay(), 999_999);

        // Fresh snapshot for clock_id = 200 IS applied.
        let mut snap_new = SyncSnapshot::EMPTY;
        snap_new.valid = true;
        snap_new.path_ns = 456_789;
        net_end
            .incoming
            .put(Incoming::SyncUpdate {
                clock_id: 200,
                snapshot: snap_new,
            })
            .ok();
        audio.cycle(&mut out, 768, 25_333_333);
        assert_eq!(audio.playback().receiver().delay(), 456_789);
    }

    #[test]
    fn peer_probe_still_answered_when_audio_buffers_are_exhausted() {
        let loopback: SocketAddr = "127.0.0.1:0".parse().expect("loopback");
        let rx_sock = Socket::bind(loopback).expect("rx");
        let rx_addr = rx_sock.address().expect("rx addr");
        let peer_sock = UdpSocket::bind(loopback).expect("peer");
        peer_sock
            .set_read_timeout(Some(Duration::from_secs(1)))
            .expect("timeout");
        let peer_addr = peer_sock.local_addr().expect("peer addr");

        // Zero spare audio buffers (`buffers: 0`) forces overflow path.
        let sizes = Sizes {
            buffers: 0,
            datagram: 2_048,
            messages: 8,
        };
        let (net_end, _audio_end) = link(sizes);
        let mut cfg = NetConfig::peer(3, 1, sizes.datagram);
        cfg.peers.push(PeerConfig {
            identity: 2,
            address: peer_addr,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        let mut net = ReceiverNetwork::with_config(rx_sock, net_end, &cfg);

        let probe = PeerProbe {
            stream: 3,
            prober: 2,
            target: 1,
            sequence: 9,
        };
        let mut buf = [0u8; packet::PEER_PROBE];
        let len = write_peer_probe(&probe, &mut buf).expect("probe");
        peer_sock.send_to(&buf[..len], rx_addr).expect("send probe");
        std::thread::sleep(Duration::from_millis(5));
        net.turn(0).expect("turn");
        assert_eq!(net.counts().peer_probes_answered, 1);

        let mut reply = [0u8; packet::PEER_ECHO];
        let (rlen, _) = peer_sock.recv_from(&mut reply).expect("recv peer echo");
        let echo = parse_peer_echo(&reply[..rlen]).expect("parse peer echo");
        assert_eq!(echo.sequence, 9);
        assert_eq!(echo.responder, 1);
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
        assert_eq!(net.bridge.engine.sender, Some(legit_addr));
        assert_eq!(net.bridge.engine.sender_timeline, Some(10));

        // Packet with wrong sample rate is rejected at network ingress.
        let before_other = net.counts().other;
        stray
            .send_to(&audio_packet(3, 10, 240, 44_100, 240), rx_addr)
            .expect("send bad rate");
        net.turn(0).expect("turn 3");
        assert_eq!(net.counts().other, before_other + 1);
        assert_eq!(net.bridge.engine.sender, Some(legit_addr));

        // Single stray packet with a different timeline must NOT hijack `sender`.
        stray
            .send_to(&audio_packet(3, 99, 0, 48_000, 240), rx_addr)
            .expect("send stray");
        net.turn(0).expect("turn 4");
        audio.cycle(&mut out, 256, 6_333_333);
        net.turn(0).expect("turn 5");
        assert_eq!(net.bridge.engine.sender, Some(legit_addr));
        assert_eq!(net.bridge.engine.sender_timeline, Some(10));
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
        net.bridge.engine.sender = Some(sender.local_addr().expect("addr"));
        // Even if `length` were artificially tiny (below REPORT + NEEDS),
        // `send_report()` pads to at least `REPORT + NEEDS` so needs are never
        // dropped.
        net.bridge.engine.length = 32;
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
        net.bridge
            .engine
            .send_report(&outgoing, &mut crate::socket::SocketSink(&mut net.socket))
            .expect("send report");
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

    #[test]
    fn sync_mode_default_is_peer() {
        assert_eq!(SyncMode::default(), SyncMode::Peer);
    }

    #[test]
    fn sender_clock_id_change_resets_sync_and_fences_stale_relays() {
        // Mutation 5: dropping `sync.reset_sender_clock()` on sender reboot
        // leaves the old sender clock snapshot active and accepts old-clock
        // relayed sender edges.
        let mut cfg = NetConfig::peer(3, 101, 2_048);
        let sender_addr: SocketAddr = "127.0.0.1:41000".parse().expect("sender");
        let peer_addr: SocketAddr = "127.0.0.1:41001".parse().expect("peer");
        cfg.peers.push(PeerConfig {
            identity: 102,
            address: peer_addr,
            weight_q16: WEIGHT_UNITY_Q16,
        });
        let mut engine = ReceiverNetEngine::new(&cfg);
        let mut sink = RecordingSink::new();

        // Confirm timeline 10 on sender clock_id = 1.
        let confirmed1 = ConfirmedState {
            attached: true,
            active: true,
            timeline: 10,
            clock_id: 1,
            rate: 48_000,
            channels: 2,
        };
        let audio1 = audio_packet(3, 10, 0, 48_000, 240);
        let _ = engine.on_datagram(
            sender_addr,
            &audio1,
            1_000_000,
            1_000_000,
            confirmed1,
            true,
            &mut sink,
        );
        // Feed one sender report departure + echo on clock_id 1 (offset +50 s).
        let _ = engine.on_departure(1, 100_000_000);
        let mut echo_buf = [0u8; packet::ECHO];
        let echo_len = packet::write_echo(
            &Echo {
                stream: 3,
                receiver: 101,
                sequence: 1,
                arrival: 50_100_100_000,
                departure: 50_100_100_000,
            },
            &mut echo_buf,
        )
        .expect("echo");
        let _ = engine.on_datagram(
            sender_addr,
            &echo_buf[..echo_len],
            100_200_000,
            100_200_000,
            confirmed1,
            true,
            &mut sink,
        );
        assert!(engine.sync_snapshot().is_some_and(|s| s.valid));
        assert!(engine.take_sync_update().is_some());

        // Sender reboots with clock_id = 2 -> sync_confirmed must reset sync
        // immediately so the old +50 s snapshot is invalidated.
        let confirmed2 = ConfirmedState {
            clock_id: 2,
            timeline: 11,
            ..confirmed1
        };
        engine.sync_confirmed(confirmed2);
        assert!(
            engine.sync_snapshot().is_some_and(|s| !s.valid),
            "sender clock_id change must reset Sync snapshot"
        );
        // A stale PeerRelay tagged with old sender_clock_id = 1 must NOT
        // re-inject old sender offset edges.
        let mut stale = packet::PeerRelay::EMPTY;
        stale.stream = 3;
        stale.sender = 102;
        stale.sequence = 1;
        stale.sender_clock_id = 1;
        stale.count = 1;
        stale.edges[0] = packet::RelayEdge {
            from_id: 0,
            to_id: 102,
            offset_ns: -50_000_000_000,
            variance_ns2: 25_000_000,
            age_ns: 1_000_000,
        };
        let mut relay_buf = [0u8; packet::PEER_RELAY_MAX];
        let relay_len = write_peer_relay(&stale, &mut relay_buf).expect("relay");
        let _ = engine.on_datagram(
            peer_addr,
            &relay_buf[..relay_len],
            200_000_000,
            200_000_000,
            confirmed2,
            true,
            &mut sink,
        );
        assert!(
            engine.sync_snapshot().is_some_and(|s| !s.valid),
            "stale PeerRelay with old sender_clock_id must be ignored after reboot"
        );
    }
}
