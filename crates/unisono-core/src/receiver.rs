// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Receiver state machine: timeline adoption, monotonic playhead management,
//! schedule tracking, and playback cycle planning.
//!
//! Operates statelessly with respect to sessions: adopts a newer timeline
//! immediately or switches after the active timeline goes silent. The playhead
//! advances strictly monotonically so every frame index is delivered at most
//! once (held, concealed, or skipped); sustained arrival of only behind-playhead
//! packets triggers a fresh restart after `silence`.
//!
//! Supports both the unified [`SyncSnapshot`] / `ModalPlayer` synchronization
//! pipeline (`use_sync = true`) and the legacy one-way lower-hull clock
//! estimator (`relation::Estimator`) plus report/echo RTT path-delay estimate.

use crate::answers::{Answer, Answers};
use crate::arrivals::Arrivals;
use crate::packet::{Audio, Echo, FLAG_STAMPED, Report};
use crate::player::{ModalPlayer, ModalRegulation, Plan, Player, Regulation};
use crate::presence::{Marked, Presence};
use crate::relation::{Estimator, Line, Sample};
use crate::sync::SyncSnapshot;
use crate::timing::{Position, Schedule, Step, due, sender_time};

/// The number of nanoseconds in a millisecond.
const MILLISECOND: i64 = 1_000_000;

/// The length of a window of the answers to reports: eight seconds. Eight
/// windows are kept, so the shortest time there and back is that of the
/// last 56 to 64 seconds.
const ROUND_WINDOW: i64 = 8_000_000_000;

/// The number of windows of answers that are kept.
const ROUND_WINDOWS: usize = 8;

/// What a receiver did with a packet.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Heard {
    /// The packet is of a timeline that the receiver does not follow, and
    /// nothing was done with it.
    pub ignored: bool,
    /// The receiver began to follow the packet's timeline with this packet.
    pub adopted: bool,
    /// The receiver started anew at this packet, because the frames that
    /// arrive had been behind its playhead for too long.
    pub restarted: bool,
    /// What became of the packet's frames.
    pub marked: Marked,
}

/// A run of frames at the playhead that are all held or all absent.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Segment {
    /// The index of the first frame of the run.
    pub first: u64,
    /// The number of frames in the run.
    pub frames: u32,
    /// Whether the frames are held. Absent frames are to be concealed.
    pub held: bool,
}

/// The settings of a receiver.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Settings {
    /// The stream identifier that this receiver accepts. Packets and echoes
    /// carrying a different stream identifier are ignored.
    pub stream: u16,
    /// A number that tells this receiver from the others of the stream.
    pub identity: u64,
    /// After how many nanoseconds without a packet of the followed timeline
    /// the receiver takes up another, and after how many without a frame at
    /// or ahead of its playhead it starts anew.
    pub silence: i64,
    /// The largest slope of its estimates of clocks, in nanoseconds per
    /// second.
    pub limit: i64,
    /// How it steers its playback.
    pub regulation: Regulation,
}

/// The receiver of a stream.
///
/// It holds up to `64 * N` frames ahead of the playhead, remembers `M`
/// samples for its estimate of the sender's clock, and keeps the arrivals of
/// the last `K` packets.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Receiver<const N: usize, const M: usize, const K: usize> {
    /// The stream identifier that this receiver accepts.
    stream: u16,
    /// Whether a timeline is followed.
    following: bool,
    /// The timeline that is followed.
    timeline: u64,
    /// The sender clock identifier of the followed timeline.
    clock_id: u32,
    /// Whether another timeline has been seen once and awaits a second packet
    /// before switching.
    has_candidate: bool,
    /// The timeline awaiting a second packet for confirmation.
    candidate: u64,
    /// The receiver's clock when a packet of the followed timeline last
    /// arrived.
    heard: i64,
    /// The receiver's clock when a packet last arrived that had a frame at
    /// or ahead of the playhead.
    fresh: i64,
    /// How long the followed timeline is silent before any other is taken
    /// up, in nanoseconds.
    silence: i64,
    /// The largest slope of the estimate of the sender's clock, in
    /// nanoseconds per second.
    limit: i64,
    /// The receiver's estimate of the smallest delay of a packet from the
    /// sender, in nanoseconds.
    path: i64,
    presence: Presence<N>,
    /// The receiver's clock minus the sender's, over the sender's clock,
    /// from the stamps of audio packets.
    clock: Estimator<M>,
    arrived: Arrivals<K>,
    /// When the frames that are being played are due.
    schedule: Option<Schedule>,
    /// What a packet further on says, when it holds the level on another
    /// line than `schedule`: a level that begins to move, or stops. It
    /// comes into use when the position that is due reaches `next_from`,
    /// the index of the first packet on its line, so that every frame is
    /// played at the level that the sender held for it.
    next: Option<Schedule>,
    next_from: u64,
    /// The same for a second change of the level's course, further on
    /// still: a move of the level has a start and an end, and both can be
    /// ahead of the frames being played.
    after: Option<Schedule>,
    after_from: u64,
    /// Whether playback uses snapshots from [`crate::sync::Sync`] and
    /// [`ModalPlayer`] instead of the legacy lower-hull estimator.
    use_sync: bool,
    /// Latest clock synchronization snapshot from [`crate::sync::Sync`].
    sync_snapshot: SyncSnapshot,
    /// Modal playback regulator used when `use_sync` is enabled.
    modal_player: ModalPlayer,
    player: Player,
    /// A number that tells this receiver from the others of the stream.
    identity: u64,
    /// The number of the next report.
    reports: u64,
    /// When the last reports left, by their numbers.
    departures: Arrivals<K>,
    /// The answers to reports that went fastest there and back.
    answers: Answers<ROUND_WINDOWS>,
}

/// How long a receiver remembers samples of the sender's clock, in
/// nanoseconds, as a header gives it.
fn span_of(header: &Audio) -> i64 {
    // A 32-bit number of milliseconds: no wrapping.
    (header.span as i64).wrapping_mul(MILLISECOND)
}

/// Half of a delay there and back, and none for one below zero, which comes
/// from stamps that are wrong.
fn halved(both: i64) -> i64 {
    if both < 0 { 0 } else { both.wrapping_shr(1) }
}

impl<const N: usize, const M: usize, const K: usize> Receiver<N, M, K> {
    /// A receiver with these settings that follows no timeline yet.
    #[must_use]
    pub fn new(settings: Settings) -> Self {
        Receiver {
            stream: settings.stream,
            following: false,
            timeline: 0,
            clock_id: 0,
            has_candidate: false,
            candidate: 0,
            heard: 0,
            fresh: 0,
            silence: settings.silence,
            limit: settings.limit,
            path: 0,
            presence: Presence::new(),
            clock: Estimator::new(0, settings.limit),
            arrived: Arrivals::new(),
            schedule: None,
            next: None,
            next_from: 0,
            after: None,
            after_from: 0,
            player: Player::new(settings.regulation),
            identity: settings.identity,
            reports: 0,
            departures: Arrivals::new(),
            answers: Answers::new(ROUND_WINDOW),
            use_sync: false,
            sync_snapshot: SyncSnapshot::EMPTY,
            modal_player: ModalPlayer::new(ModalRegulation::from_single(settings.regulation)),
        }
    }

    /// Enables [`crate::sync::Sync`]-driven clock estimation and configures
    /// [`ModalPlayer`] with `regulation`.
    pub fn enable_sync(&mut self, regulation: ModalRegulation) {
        self.use_sync = true;
        self.modal_player.set_regulation(regulation);
    }

    /// Updates the [`ModalPlayer`] regulation parameters without changing
    /// active playback continuity.
    pub fn set_modal_regulation(&mut self, regulation: ModalRegulation) {
        self.modal_player.set_regulation(regulation);
    }

    /// Applies an O(1) clock synchronization snapshot published by
    /// [`crate::sync::Sync`] on the network thread.
    pub fn apply_sync(&mut self, snapshot: SyncSnapshot) {
        self.use_sync = true;
        self.sync_snapshot = snapshot;
        if snapshot.valid {
            self.path = snapshot.path_ns;
        }
    }

    /// Latest [`SyncSnapshot`] applied to this receiver.
    #[must_use]
    pub fn sync_snapshot(&self) -> SyncSnapshot {
        self.sync_snapshot
    }

    /// Whether this receiver is using [`crate::sync::Sync`] snapshots rather
    /// than the legacy lower-hull estimator.
    #[must_use]
    pub fn uses_sync(&self) -> bool {
        self.use_sync
    }

    /// Sender clock identifier of the followed timeline, if any.
    #[must_use]
    pub fn clock_id(&self) -> Option<u32> {
        if self.following {
            Some(self.clock_id)
        } else {
            None
        }
    }

    /// Sets the receiver's estimate of the smallest delay of a packet from
    /// the sender, in nanoseconds. A receiver whose reports are answered
    /// finds it by itself.
    pub fn path(&mut self, path: i64) {
        self.path = path;
    }

    /// The receiver's estimate of the smallest delay of a packet from the
    /// sender, in nanoseconds.
    #[must_use]
    pub fn delay(&self) -> i64 {
        self.path
    }

    /// The timeline that is followed, if any.
    #[must_use]
    pub fn timeline(&self) -> Option<u64> {
        if self.following {
            Some(self.timeline)
        } else {
            None
        }
    }

    /// The index of the next frame for the device.
    #[must_use]
    pub fn playhead(&self) -> u64 {
        self.presence.base()
    }

    /// Whether there is room for the frame at `index`: the caller keeps the
    /// samples of exactly these frames.
    #[must_use]
    pub fn covers(&self, index: u64) -> bool {
        self.following && self.presence.covers(index)
    }

    /// The estimate of the receiver's clock minus the sender's clock, as a
    /// line over the sender's clock, once there is one.
    #[must_use]
    pub fn clock(&self) -> Option<Line> {
        self.clock.line()
    }

    /// When the frames of the followed timeline are due, once a packet has
    /// said it.
    #[must_use]
    pub fn schedule(&self) -> Option<Schedule> {
        self.schedule
    }

    /// Whether a packet of `timeline` that arrives at `arrival` makes the
    /// receiver follow that timeline instead of what it follows now.
    ///
    /// A receiver that follows a timeline takes up another only at its
    /// second packet in a row, so that one stray or forged packet does not
    /// move it.
    fn adopts(&self, timeline: u64, arrival: i64) -> bool {
        if !self.following {
            return true;
        }
        if timeline == self.timeline {
            return false;
        }
        if !self.has_candidate || self.candidate != timeline {
            return false;
        }
        timeline > self.timeline || arrival.saturating_sub(self.heard) >= self.silence
    }

    /// Begins to follow the timeline of `header`, with nothing held. When the
    /// timeline is on the clock of the one before, as after a restart of
    /// the sender's capture, the estimate of that clock stays and only the
    /// numbering of its windows starts again. On another clock the estimate,
    /// its kept answers and the in-flight report departures are dropped,
    /// while the delay of the path stays as a prior until an echo on the new
    /// clock arrives.
    fn adopt(&mut self, header: &Audio) {
        let was_following = self.following;
        let same_clock = was_following && header.clock == self.clock_id;
        self.following = true;
        self.timeline = header.timeline;
        self.clock_id = header.clock;
        self.has_candidate = false;
        self.presence.restart(header.index);
        self.arrived = Arrivals::new();
        self.schedule = None;
        self.next = None;
        self.after = None;
        self.player.stop();
        self.modal_player.stop();
        if same_clock {
            self.clock.remember(span_of(header));
            self.clock.reset_window();
        } else {
            self.clock = Estimator::new(span_of(header), self.limit);
            self.answers.clear();
            self.departures = Arrivals::new();
            self.sync_snapshot = SyncSnapshot::EMPTY;
        }
    }

    /// When the earlier packet arrived whose departure `header` carries, if
    /// it carries one and that arrival is still kept.
    fn stamped_arrival(&self, header: &Audio) -> Option<i64> {
        if header.flags & FLAG_STAMPED == 0 {
            return None;
        }
        self.arrived.find(header.stamped_index)
    }

    /// Gives the estimate of the sender's clock the sample of the earlier
    /// packet whose departure `header` carries and which arrived at
    /// `arrived`.
    fn sample(&mut self, header: &Audio, arrived: i64) {
        let sample = Sample {
            time: header.stamped_departure,
            value: arrived.saturating_sub(header.stamped_departure),
        };
        // A window of no frames makes every packet a window.
        let window = header
            .stamped_index
            .checked_div(header.window as u64)
            .unwrap_or(header.stamped_index);
        self.clock.observe(window, sample);
    }

    /// Takes from a packet of the followed timeline what it says about the
    /// sender's clock, and keeps its arrival for a later packet to refer to.
    fn measure(&mut self, header: &Audio, arrival: i64) {
        self.clock.remember(span_of(header));
        if let Some(arrived) = self.stamped_arrival(header) {
            self.sample(header, arrived);
        }
        self.arrived.record(header.index, arrival);
    }

    /// Keeps what `header` says about when frames are due.
    ///
    /// A packet arrives well before its frames are played. As long as it
    /// holds the level on the line of the newest schedule kept, it takes
    /// that schedule's place: it says the same of the frames it stands for,
    /// with a later capture time. When the level takes another course at
    /// the packet, a slope that begins or ends, what it says holds from its
    /// index on and is kept until the position due gets there. Two such
    /// changes are kept, the start and the end of a move of the level; at a
    /// third, the first comes into use at once, which moves the frames being
    /// played by at most what the level changes over the time by which
    /// packets are ahead. A packet from before the newest schedule kept
    /// says nothing new.
    fn note(&mut self, header: &Audio) {
        let said = Schedule {
            index: header.index,
            capture: header.capture,
            rate: header.rate,
            drift: header.drift,
            level: header.level,
            level_slope: header.level_slope,
        };
        let Some(used) = self.schedule else {
            self.schedule = Some(said);
            return;
        };
        let Some(next) = self.next else {
            if header.index < used.index {
                return;
            }
            if used.continues(&said) {
                self.schedule = Some(said);
            } else {
                self.next = Some(said);
                self.next_from = header.index;
            }
            return;
        };
        let Some(after) = self.after else {
            if header.index < next.index {
                return;
            }
            if next.continues(&said) {
                self.next = Some(said);
            } else {
                self.after = Some(said);
                self.after_from = header.index;
            }
            return;
        };
        if header.index < after.index {
            return;
        }
        if !after.continues(&said) {
            self.turn();
            self.after_from = header.index;
        }
        self.after = Some(said);
    }

    /// Takes the next schedule kept into use, and the one after it in its
    /// place.
    fn turn(&mut self) {
        if let Some(next) = self.next {
            self.schedule = Some(next);
        }
        self.next = self.after;
        self.next_from = self.after_from;
        self.after = None;
    }

    /// Moves the stretch forward so that it ends at the last frame of the
    /// packet with `header`, as long as the sender's clock is not known and
    /// nothing is played: the frames that will be played first are then the
    /// newest. A packet that lies more than a stretch beyond the end leaves
    /// the stretch where it is, so that a wrong header does not carry the
    /// playhead away.
    fn keep_newest(&mut self, header: &Audio) {
        if self.use_sync {
            if self.sync_snapshot.valid {
                return;
            }
        } else if self.clock.line().is_some() {
            return;
        }
        let width = self.presence.width();
        if width == 0 {
            return;
        }
        let base = self.presence.base();
        let end = header.index.saturating_add(header.frames as u64);
        let stretch_end = base.saturating_add(width);
        let limit = stretch_end.saturating_add(width);
        if header.index > base && end > stretch_end && header.index <= limit {
            let target = end.saturating_sub(width);
            let new_base = if target < header.index {
                target
            } else {
                header.index
            };
            self.presence.advance(new_base);
        }
    }

    /// Whether the frames of a packet that arrived at `arrival` and were
    /// marked as `marked` show that the playhead is wrong: all of them are
    /// behind it, and no packet has had a frame at or ahead of it for the
    /// set time.
    fn stale(&mut self, marked: &Marked, arrival: i64) -> bool {
        // The clock is not behind the last such arrival; a record that says
        // so is wrong.
        if self.fresh > arrival {
            self.fresh = arrival;
        }
        if marked.late == 0 || marked.stored > 0 || marked.duplicate > 0 || marked.early > 0 {
            return false;
        }
        arrival.saturating_sub(self.fresh) >= self.silence
    }

    /// Starts anew at the frames of the packet with `header`: the playhead
    /// is at its first frame, nothing but its frames is held, and playback
    /// starts on the schedule.
    fn renew(&mut self, header: &Audio) -> Marked {
        self.presence.restart(header.index);
        self.player.stop();
        self.modal_player.stop();
        // The index has started again, so what earlier packets said about
        // when frames are due no longer holds.
        self.schedule = None;
        self.next = None;
        self.after = None;
        // The windows of the clock's estimate are numbered by the index,
        // which has started again.
        self.clock.reset_window();
        self.presence.mark(header.index, header.frames as u32)
    }

    /// Takes in that a packet with `header` arrived at `arrival` and its
    /// frames were marked as `marked`. A packet with a frame in the stretch,
    /// or a packet without frames whose index the stretch covers, is part of
    /// the stream as the receiver holds it, and updates the schedule.
    fn refresh(&mut self, header: &Audio, marked: &Marked, arrival: i64) {
        if marked.stored > 0
            || marked.duplicate > 0
            || (header.frames == 0 && self.presence.covers(header.index))
        {
            self.fresh = arrival;
            self.note(header);
        } else if marked.early > 0 {
            self.fresh = arrival;
        }
    }

    /// Takes in a packet of the followed timeline.
    fn accept(&mut self, header: &Audio, arrival: i64, adopted: bool) -> Heard {
        self.heard = arrival;
        self.keep_newest(header);
        if !self.use_sync {
            self.measure(header, arrival);
        }
        let first = self.presence.mark(header.index, header.frames as u32);
        let restarted = self.stale(&first, arrival);
        let marked = if restarted { self.renew(header) } else { first };
        self.refresh(header, &marked, arrival);
        Heard {
            ignored: false,
            adopted,
            restarted,
            marked,
        }
    }

    /// Takes in the packet with `header` that arrived when the receiver's
    /// clock read `arrival`, and says what was done with it.
    pub fn packet(&mut self, header: &Audio, arrival: i64) -> Heard {
        let ignored = Heard {
            ignored: true,
            adopted: false,
            restarted: false,
            marked: Marked {
                stored: 0,
                duplicate: 0,
                late: 0,
                early: 0,
            },
        };
        if header.stream != self.stream {
            return ignored;
        }
        // The clock is not behind the last arrival; a record that says so is
        // wrong, and is put right here so that silence is noticed.
        if self.heard > arrival {
            self.heard = arrival;
        }
        let adopted = self.adopts(header.timeline, arrival);
        if adopted {
            self.adopt(header);
        } else if header.timeline != self.timeline {
            self.has_candidate = true;
            self.candidate = header.timeline;
            return ignored;
        } else {
            self.has_candidate = false;
        }
        self.accept(header, arrival, adopted)
    }

    /// The next report for the followed stream, once a timeline is followed.
    /// After it has been sent, [`Receiver::reported`] takes in when it left.
    pub fn report(&mut self) -> Option<Report> {
        if !self.following {
            return None;
        }
        let sequence = self.reports;
        self.reports = self.reports.wrapping_add(1);
        Some(Report {
            stream: self.stream,
            timeline: self.timeline,
            receiver: self.identity,
            sequence,
        })
    }

    /// Takes in that the report with number `sequence` left when the
    /// receiver's clock read `departure`.
    pub fn reported(&mut self, sequence: u64, departure: i64) {
        self.departures.record(sequence, departure);
    }

    /// Takes in the sender's answer to a report. With the time at which the
    /// report left and the estimate of the sender's clock it gives a delay
    /// there and back, and the smallest such delay of the last minute, halved,
    /// is the delay of the path from the sender. An answer to another stream
    /// or receiver, to a report whose departure is no longer kept, or that
    /// comes before the sender's clock is known, is left out.
    pub fn echo(&mut self, echo: &Echo) {
        if !self.following || echo.stream != self.stream || echo.receiver != self.identity {
            return;
        }
        let Some(departure) = self.departures.find(echo.sequence) else {
            return;
        };
        let Some(forward) = self.clock.line() else {
            return;
        };
        let answer = Answer {
            departure,
            arrival: echo.arrival,
        };
        self.answers.observe(answer, &forward);
        if let Some(shortest) = self.answers.shortest(&forward) {
            self.path = halved(shortest);
        }
    }

    /// Plans one cycle of the device: `frames` output frames, the first of
    /// which leaves the device when the receiver's clock reads `time`, and
    /// which take `duration` nanoseconds on that clock. Nothing is played,
    /// and the plan has no frames, as long as no timeline is followed, the
    /// sender's clock is not known, or no frame of the timeline is due.
    pub fn cycle(&mut self, time: i64, duration: i64, frames: u32) -> Plan {
        let idle = Plan {
            frames: 0,
            start: Position {
                frame: 0,
                fraction: 0,
            },
            step: Step::UNITY,
            jumped: false,
        };
        if !self.following {
            return idle;
        }
        let Some(schedule) = self.schedule else {
            return idle;
        };
        let end_time = time.saturating_add(duration);
        let (first, last) = if self.use_sync {
            if !self.sync_snapshot.valid {
                return idle;
            }
            (
                self.sync_snapshot.sender_time(time),
                self.sync_snapshot.sender_time(end_time),
            )
        } else {
            let Some(line) = self.clock.line() else {
                return idle;
            };
            (
                sender_time(&line, self.path, time),
                sender_time(&line, self.path, end_time),
            )
        };
        let Some(now) = due(&schedule, first) else {
            return idle;
        };
        // The position due has reached the packet at which the level takes
        // another course: from here on that packet's schedule holds.
        let Some((schedule, now)) = self.reached(schedule, now, first) else {
            return idle;
        };
        let Some(then) = due(&schedule, last) else {
            return idle;
        };
        if self.use_sync {
            let com_now = self.sync_snapshot.common_offset_ns(time);
            let com_then = self.sync_snapshot.common_offset_ns(end_time);
            self.modal_player.cycle(
                now,
                then,
                frames,
                duration,
                &schedule,
                self.sync_snapshot.peer_active,
                self.sync_snapshot.epoch,
                com_now,
                com_then,
            )
        } else {
            self.player
                .cycle(now, then, frames, duration, schedule.level_slope)
        }
    }

    /// The position that is due when the receiver's clock reads `time`, by
    /// the schedule in use; nothing while no timeline is followed, the
    /// sender's clock is not known, or no frame of the timeline is due.
    #[must_use]
    pub fn due_at(&self, time: i64) -> Option<Position> {
        if !self.following {
            return None;
        }
        let Some(schedule) = self.schedule else {
            return None;
        };
        let sender_now = if self.use_sync {
            if !self.sync_snapshot.valid {
                return None;
            }
            self.sync_snapshot.sender_time(time)
        } else {
            let Some(line) = self.clock.line() else {
                return None;
            };
            sender_time(&line, self.path, time)
        };
        due(&schedule, sender_now)
    }

    /// Advances through any queued schedule whose starting index the due
    /// position has reached, returning the active schedule and its position
    /// due at `first`. Returns `None` when a reached schedule has no position
    /// due at `first`.
    fn reached(
        &mut self,
        schedule: Schedule,
        now: Position,
        first: i64,
    ) -> Option<(Schedule, Position)> {
        let mut current = schedule;
        let mut current_now = now;
        // At most two schedules (`next` and `after`) can be queued.
        if let Some(next) = self.next
            && current_now.frame >= self.next_from
        {
            self.turn();
            let Some(turned) = due(&next, first) else {
                return None;
            };
            current = next;
            current_now = turned;
        }
        if let Some(next) = self.next
            && current_now.frame >= self.next_from
        {
            self.turn();
            let Some(turned) = due(&next, first) else {
                return None;
            };
            current = next;
            current_now = turned;
        }
        Some((current, current_now))
    }

    /// Moves the playhead forward by `frames`.
    fn pass(&mut self, frames: u32) {
        let base = self.presence.base();
        self.presence.advance(base.saturating_add(frames as u64));
    }

    /// Takes the next run of frames for the device: up to `limit` frames
    /// from the playhead on that are all held or all absent. The playhead
    /// moves past them. Without a timeline the run is empty.
    pub fn take(&mut self, limit: u32) -> Segment {
        let first = self.presence.base();
        if !self.following {
            return Segment {
                first,
                frames: 0,
                held: false,
            };
        }
        let run = self.presence.run(first, limit);
        if run > 0 {
            self.pass(run);
            return Segment {
                first,
                frames: run,
                held: true,
            };
        }
        let gap = self.presence.gap(first, limit);
        self.pass(gap);
        Segment {
            first,
            frames: gap,
            held: false,
        }
    }

    /// Moves the playhead forward to `to` without giving the frames before
    /// it to the device, and returns how many frames that skips. A `to` that
    /// is not ahead of the playhead skips nothing: the playhead never moves
    /// back.
    pub fn skip(&mut self, to: u64) -> u64 {
        let base = self.presence.base();
        if !self.following || to <= base {
            return 0;
        }
        self.presence.advance(to);
        to.wrapping_sub(base)
    }
}

#[cfg(test)]
mod tests {
    use super::{Heard, Receiver, Segment, Settings};
    use crate::packet::Echo;
    use crate::packet::{Audio, FLAG_STAMPED, Format};
    use crate::player::Regulation;
    use crate::presence::Marked;
    use crate::timing::Position;

    const SILENCE: i64 = 1_000_000_000;

    fn header(timeline: u64, index: u64, frames: u16) -> Audio {
        Audio {
            stream: 1,
            timeline,
            index,
            capture: 0,
            drift: 0,
            rate: 48_000,
            frames,
            channels: 2,
            format: Format::Signed16,
            level: 20_000_000,
            level_slope: 0,
            span: 11_000,
            window: 480,
            flags: 0,
            protection: 0,
            stamped_index: 0,
            stamped_departure: 0,
            clock: 1,
        }
    }

    fn stored(frames: u32) -> Marked {
        Marked {
            stored: frames,
            ..Marked::default()
        }
    }

    fn receiver() -> Receiver<4, 8, 4> {
        Receiver::new(Settings {
            stream: 1,
            identity: 42,
            silence: SILENCE,
            limit: 200_000,
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
        })
    }

    #[test]
    fn the_first_packet_starts_a_timeline_at_its_index() {
        let mut receiver = receiver();
        assert_eq!(receiver.timeline(), None);
        assert_eq!(receiver.take(10).frames, 0);
        let heard = receiver.packet(&header(7, 4_800, 10), 0);
        assert_eq!(
            heard,
            Heard {
                ignored: false,
                adopted: true,
                restarted: false,
                marked: stored(10)
            }
        );
        assert_eq!(receiver.timeline(), Some(7));
        assert_eq!(receiver.playhead(), 4_800);
        assert!(receiver.covers(4_800) && !receiver.covers(4_799));
    }

    #[test]
    fn frames_pass_the_playhead_once_and_in_order() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        // The second packet is lost; the third arrives.
        receiver.packet(&header(7, 20, 10), 1);
        let mut segments = [Segment {
            first: 0,
            frames: 0,
            held: false,
        }; 4];
        for segment in &mut segments {
            *segment = receiver.take(16);
        }
        let expected = [
            (0, 10, true),
            (10, 10, false),
            (20, 10, true),
            (30, 16, false),
        ];
        for (segment, (first, frames, held)) in segments.iter().zip(expected) {
            assert_eq!(
                *segment,
                Segment {
                    first,
                    frames,
                    held
                }
            );
        }
        assert_eq!(receiver.playhead(), 46);
        // The lost packet arrives after its frames were due.
        let heard = receiver.packet(&header(7, 10, 10), 2);
        assert_eq!(
            heard.marked,
            Marked {
                late: 10,
                ..Marked::default()
            }
        );
    }

    #[test]
    fn a_run_is_cut_at_the_limit() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        assert_eq!(receiver.take(4).frames, 4);
        assert_eq!(receiver.take(0).frames, 0);
        assert_eq!(receiver.playhead(), 4);
    }

    #[test]
    fn a_skip_moves_the_playhead_forward_only() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        assert_eq!(receiver.skip(6), 6);
        assert_eq!(receiver.skip(3), 0);
        assert_eq!(receiver.playhead(), 6);
        assert_eq!(receiver.take(16).frames, 4);
    }

    #[test]
    fn a_later_timeline_requires_confirmation_and_an_earlier_one_is_ignored() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        // One stray packet of a later timeline does not move the receiver.
        let stray = receiver.packet(&header(9, 100, 10), 1);
        assert!(stray.ignored && !stray.adopted);
        assert_eq!((receiver.timeline(), receiver.playhead()), (Some(7), 0));
        // A second packet confirms the later timeline.
        let heard = receiver.packet(&header(9, 110, 10), 2);
        assert!(heard.adopted && !heard.ignored);
        assert_eq!((receiver.timeline(), receiver.playhead()), (Some(9), 110));
        // Packets of the old timeline still in flight are ignored.
        let heard = receiver.packet(&header(7, 10, 10), 3);
        assert!(heard.ignored && !heard.adopted);
        assert_eq!(receiver.timeline(), Some(9));
    }

    #[test]
    fn a_packet_of_the_followed_timeline_clears_a_stray_candidate() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        assert!(receiver.packet(&header(99, 0, 10), 1).ignored);
        // Normal traffic clears the candidate, so another stray packet later
        // does not add up to a switch.
        assert!(!receiver.packet(&header(7, 10, 10), 2).ignored);
        assert!(receiver.packet(&header(99, 10, 10), 3).ignored);
        assert_eq!(receiver.timeline(), Some(7));
    }

    #[test]
    fn packets_and_echoes_of_another_stream_are_ignored() {
        let mut receiver = receiver();
        let mut wrong = header(7, 0, 10);
        wrong.stream = 2;
        assert!(receiver.packet(&wrong, 0).ignored);
        assert_eq!(receiver.timeline(), None);

        receiver.packet(&header(7, 0, 10), 0);
        receiver.path(77);
        let report = receiver.report().expect("a timeline is followed");
        assert_eq!(report.stream, 1);
        receiver.reported(report.sequence, 1_000);
        receiver.echo(&Echo {
            stream: 2,
            receiver: 42,
            sequence: report.sequence,
            arrival: 5_000,
            departure: 5_000,
        });
        assert_eq!(receiver.delay(), 77);
        // Even a higher timeline on the wrong stream leaves the receiver alone.
        let mut wrong_later = header(99, 0, 10);
        wrong_later.stream = 2;
        assert!(receiver.packet(&wrong_later, 1).ignored);
        assert!(receiver.packet(&wrong_later, 2).ignored);
        assert_eq!(receiver.timeline(), Some(7));
    }

    #[test]
    fn an_earlier_timeline_is_followed_once_the_other_is_silent() {
        let mut receiver = receiver();
        receiver.packet(&header(9, 0, 10), 0);
        assert!(receiver.packet(&header(7, 0, 10), SILENCE - 1).ignored);
        let heard = receiver.packet(&header(7, 10, 10), SILENCE);
        assert!(heard.adopted);
        assert_eq!((receiver.timeline(), receiver.playhead()), (Some(7), 10));
    }

    #[test]
    fn a_record_of_the_last_arrival_that_lies_ahead_does_not_block_another_timeline() {
        let mut receiver = receiver();
        receiver.packet(&header(9, 0, 10), 0);
        receiver.heard = i64::MAX;
        assert!(receiver.packet(&header(7, 0, 10), 5).ignored);
        assert!(receiver.packet(&header(7, 10, 10), 5 + SILENCE).adopted);
    }

    #[test]
    fn stamps_of_earlier_packets_give_the_sender_s_clock() {
        // The receiver's clock is 5 ms ahead of the sender's, and every
        // packet takes 100 microseconds.
        let mut receiver = receiver();
        let period = 10_000_000i64;
        for packet in 0..200u64 {
            let departure = i64::try_from(packet).unwrap_or(0) * period;
            let mut header = header(7, packet * 480, 480);
            if packet > 0 {
                header.flags = FLAG_STAMPED;
                header.stamped_index = (packet - 1) * 480;
                header.stamped_departure = departure - period;
            }
            receiver.packet(&header, departure + 5_000_000 + 100_000);
        }
        let line = receiver.clock().expect("a line after many windows");
        assert_eq!(line.eval(1_000_000_000), 5_100_000);
    }

    #[test]
    fn the_schedule_is_that_of_the_last_packet_with_a_frame_in_the_stretch() {
        let mut receiver = receiver();
        let mut first = header(7, 100, 10);
        first.capture = 1_000;
        receiver.packet(&first, 0);
        // A packet whose frames are all beyond the stretch, as a damaged
        // header may claim, does not say when frames are due.
        let mut beyond = header(7, 1_000_000, 10);
        beyond.capture = 77;
        receiver.packet(&beyond, 1);
        let schedule = receiver.schedule().expect("a schedule after a packet");
        assert_eq!((schedule.index, schedule.capture), (100, 1_000));
        let mut next = header(7, 110, 10);
        next.capture = 2_000;
        receiver.packet(&next, 2);
        let schedule = receiver.schedule().expect("a schedule after a packet");
        assert_eq!((schedule.index, schedule.capture), (110, 2_000));
    }

    #[test]
    fn a_change_of_the_level_s_course_holds_from_its_packet_on() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 100, 10), 0);
        receiver.packet(&header(7, 110, 10), 1);
        assert_eq!(receiver.schedule().map(|used| used.index), Some(110));
        // At the packet with index 120 the level begins to rise by 4.8 ms a
        // second, which is 100 ns for each frame.
        let mut rising = header(7, 120, 10);
        rising.level_slope = 4_800_000;
        receiver.packet(&rising, 2);
        let mut further = header(7, 130, 10);
        further.level_slope = 4_800_000;
        further.level += 1_000;
        receiver.packet(&further, 3);
        // The frames before it are due as the packets before it said, and a
        // packet that was overtaken changes nothing.
        receiver.packet(&header(7, 112, 2), 4);
        let used = receiver.schedule().expect("a schedule");
        assert_eq!((used.index, used.level_slope), (110, 0));
        // The position due gets to the packet where the level began to
        // rise: from there on the newest packet of the rising level holds.
        let before = Position {
            frame: 119,
            fraction: u64::MAX,
        };
        assert_eq!(
            receiver.reached(used, before, 20_000_000),
            Some((used, before))
        );
        let at = Position {
            frame: 120,
            fraction: 0,
        };
        let (turned, _) = receiver.reached(used, at, 20_000_000).expect("the change");
        assert_eq!((turned.index, turned.level_slope), (130, 4_800_000));
        assert_eq!(receiver.schedule(), Some(turned));
        // A packet that goes on along the rising level takes its place.
        let mut on = header(7, 140, 10);
        on.level_slope = 4_800_000;
        on.level += 2_000;
        receiver.packet(&on, 5);
        assert_eq!(receiver.schedule().map(|used| used.index), Some(140));
    }

    #[test]
    fn the_start_and_the_end_of_a_move_are_both_kept_ahead() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 100, 10), 0);
        // The level rises by 100 ns a frame over one packet, and holds.
        let mut rising = header(7, 110, 10);
        rising.level_slope = 4_800_000;
        receiver.packet(&rising, 1);
        let mut held = header(7, 120, 10);
        held.level += 1_000;
        receiver.packet(&held, 2);
        // The frames being played are still due as the first packet said.
        let used = receiver.schedule().expect("a schedule");
        assert_eq!((used.index, used.level_slope), (100, 0));
        let at = |frame| Position { frame, fraction: 0 };
        let (turned, _) = receiver
            .reached(used, at(110), 20_000_000)
            .expect("the rise");
        assert_eq!((turned.index, turned.level_slope), (110, 4_800_000));
        assert_eq!(
            receiver.reached(turned, at(119), 20_000_000),
            Some((turned, at(119)))
        );
        let (turned, _) = receiver
            .reached(turned, at(120), 20_000_000)
            .expect("the hold");
        assert_eq!((turned.index, turned.level_slope), (120, 0));
        assert_eq!(
            receiver.reached(turned, at(200), 20_000_000),
            Some((turned, at(200)))
        );
    }

    #[test]
    fn at_a_third_change_of_course_ahead_the_first_comes_into_use() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 100, 10), 0);
        let mut rising = header(7, 110, 10);
        rising.level_slope = 4_800_000;
        receiver.packet(&rising, 1);
        let mut held = header(7, 120, 10);
        held.level += 1_000;
        receiver.packet(&held, 2);
        let mut falling = header(7, 130, 10);
        falling.level += 1_000;
        falling.level_slope = -4_800_000;
        receiver.packet(&falling, 3);
        let used = receiver.schedule().expect("a schedule");
        assert_eq!((used.index, used.level_slope), (110, 4_800_000));
        let at = |frame| Position { frame, fraction: 0 };
        let (turned, _) = receiver
            .reached(used, at(120), 20_000_000)
            .expect("the hold");
        assert_eq!((turned.index, turned.level_slope), (120, 0));
        let (turned, _) = receiver
            .reached(turned, at(130), 20_000_000)
            .expect("the fall");
        assert_eq!((turned.index, turned.level_slope), (130, -4_800_000));
    }

    #[test]
    fn reached_turns_through_both_queued_schedules_and_idles_when_none_due() {
        // Both `next` and `after` already due at `first`: turns straight to `after`.
        let mut receiver = receiver();
        receiver.packet(&header(7, 100, 10), 0);
        let mut rising = header(7, 110, 10);
        rising.level_slope = 4_800_000;
        receiver.packet(&rising, 1);
        let mut held = header(7, 120, 10);
        held.level += 1_000;
        receiver.packet(&held, 2);
        let used = receiver.schedule().expect("a schedule");
        // At first = 20_000_000 + 250_000 ns (12 frames past 110), `due(&rising)` >= 120.
        let (turned, _) = receiver
            .reached(
                used,
                Position {
                    frame: 122,
                    fraction: 0,
                },
                20_250_000,
            )
            .expect("turned to held");
        assert_eq!((turned.index, turned.level_slope), (120, 0));
        assert_eq!(receiver.schedule(), Some(turned));

        // When `next` raises the level so `due(&next, first)` is None, `reached`
        // returns None (cycle idles) instead of falling back to the old schedule.
        let mut receiver = self::receiver();
        receiver.packet(&header(7, 0, 10), 0);
        let mut raised = header(7, 10, 10);
        raised.level = 500_000_000;
        receiver.packet(&raised, 1);
        let used = receiver.schedule().expect("a schedule");
        assert_eq!(
            receiver.reached(
                used,
                Position {
                    frame: 10,
                    fraction: 0
                },
                20_000_000
            ),
            None
        );
    }

    #[test]
    fn a_playhead_that_is_ahead_of_everything_that_arrives_is_given_up() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        // The playhead is moved far ahead, as a damaged packet may cause.
        receiver.skip(1_000_000);
        // Packets go on arriving, all of them behind the playhead.
        let heard = receiver.packet(&header(7, 10, 10), SILENCE - 1);
        assert_eq!((heard.restarted, heard.marked.late), (false, 10));
        let heard = receiver.packet(&header(7, 20, 10), SILENCE);
        assert_eq!((heard.restarted, heard.marked), (true, stored(10)));
        assert_eq!(receiver.playhead(), 20);
        // One late packet among others that are in time changes nothing.
        receiver.take(10);
        receiver.packet(&header(7, 40, 10), 3 * SILENCE);
        let heard = receiver.packet(&header(7, 20, 10), 5 * SILENCE);
        assert_eq!((heard.restarted, heard.marked.late), (true, 0));
    }

    /// Feeds a receiver the packets of a sender whose clock is `offset`
    /// behind the receiver's, each of 480 frames every 10 ms with a delay of
    /// 100 microseconds, from packet `from` up to packet `to`.
    fn stream(receiver: &mut Receiver<4, 8, 4>, offset: i64, from: u64, to: u64) {
        let period = 10_000_000i64;
        for packet in from..to {
            let departure = i64::try_from(packet).unwrap_or(0) * period;
            let mut header = header(7, packet * 480, 480);
            header.capture = departure - 10_000_000;
            header.window = 4_800;
            if packet > 0 {
                header.flags = FLAG_STAMPED;
                header.stamped_index = (packet - 1) * 480;
                header.stamped_departure = departure - period;
            }
            receiver.packet(&header, departure + offset + 100_000);
        }
    }

    #[test]
    fn a_cycle_plays_the_frames_that_are_due() {
        let offset = 3_600_000_000_000i64;
        let mut receiver: Receiver<4, 8, 4> = receiver();
        // Before the sender's clock is known nothing is played.
        stream(&mut receiver, offset, 0, 5);
        assert_eq!(
            receiver.cycle(offset + 50_000_000, 5_000_000, 240).frames,
            0
        );
        stream(&mut receiver, offset, 5, 60);
        // Frame n was captured at (n / 48 - 10) ms and is due 20 ms later.
        // The estimate holds the delay of 100 microseconds, which the path
        // takes off again.
        receiver.path(100_000);
        let time = offset + 500_000_000;
        let plan = receiver.cycle(time, 5_000_000, 240);
        assert!(plan.jumped && plan.frames == 240);
        assert_eq!(plan.start.frame, (500 - 10) * 48);
        assert!(
            plan.start.fraction < 1 << 54,
            "fraction {}",
            plan.start.fraction
        );
        // The next cycle goes on where this one ended.
        let next = receiver.cycle(time + 5_000_000, 5_000_000, 240);
        assert!(!next.jumped);
        assert_eq!(next.start.frame, plan.start.frame + 240);
    }

    #[test]
    fn answered_reports_give_the_delay_of_the_path() {
        // The receiver's clock is an hour ahead of the sender's. A packet
        // takes 100 microseconds from the sender and 140 back.
        let offset = 3_600_000_000_000i64;
        let mut receiver: Receiver<4, 8, 4> = receiver();
        assert_eq!(receiver.report(), None);
        let period = 10_000_000i64;
        for packet in 0..300u64 {
            let departure = i64::try_from(packet).unwrap_or(0) * period;
            let mut header = header(7, packet * 480, 480);
            header.window = 4_800;
            if packet > 0 {
                header.flags = FLAG_STAMPED;
                header.stamped_index = (packet - 1) * 480;
                header.stamped_departure = departure - period;
            }
            let now = departure + offset + 100_000;
            receiver.packet(&header, now);
            // A report leaves with every fifth packet and is answered.
            if packet % 5 == 0 {
                let report = receiver.report().expect("a timeline is followed");
                assert_eq!(
                    (report.stream, report.timeline, report.receiver),
                    (1, 7, 42)
                );
                receiver.reported(report.sequence, now);
                receiver.echo(&Echo {
                    stream: 1,
                    receiver: 42,
                    sequence: report.sequence,
                    arrival: now - offset + 140_000,
                    departure: now - offset + 140_000,
                });
            }
        }
        // Half of 240 microseconds there and back.
        assert_eq!(receiver.delay(), 120_000);
    }

    #[test]
    fn an_answer_that_is_not_for_this_receiver_is_left_out() {
        let mut receiver: Receiver<4, 8, 4> = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        receiver.path(77);
        let report = receiver.report().expect("a timeline is followed");
        receiver.reported(report.sequence, 1_000);
        // To another receiver, and to a report that was never sent.
        for (to, sequence) in [(43, report.sequence), (42, report.sequence + 9)] {
            receiver.echo(&Echo {
                stream: 1,
                receiver: to,
                sequence,
                arrival: 5_000,
                departure: 5_000,
            });
        }
        assert_eq!(receiver.delay(), 77);
        // Reports are numbered one after the other.
        assert_eq!(
            receiver.report().map(|next| next.sequence),
            Some(report.sequence + 1)
        );
    }

    #[test]
    fn a_timeline_on_the_same_clock_keeps_the_estimate_and_any_timeline_keeps_the_path() {
        let offset = 5_000_000i64;
        let mut receiver: Receiver<4, 8, 4> = receiver();
        stream(&mut receiver, offset, 0, 60);
        receiver.path(100_000);
        let line_before = receiver.clock().expect("the clock is known");

        // Capture restart on the same sender clock (clock == 1): two packets
        // confirm timeline 9 and preserve the clock line and path estimate.
        let p0 = header(9, 0, 480);
        assert!(receiver.packet(&p0, offset + 700_000_000).ignored);
        let p1 = header(9, 480, 480);
        assert!(receiver.packet(&p1, offset + 710_000_000).adopted);
        let line_after = receiver
            .clock()
            .expect("the clock is still known after a timeline on the same clock");
        assert_eq!(line_after.eval(500_000_000), line_before.eval(500_000_000));
        assert_eq!(receiver.delay(), 100_000);

        // Another clock (clock == 2): the second packet of timeline 11 drops
        // the estimate of the clock. The delay of the path stays, because it
        // does not depend on the sender's clock.
        let mut r0 = header(11, 0, 480);
        r0.clock = 2;
        let mut r1 = header(11, 480, 480);
        r1.clock = 2;
        assert!(receiver.packet(&r0, offset + 800_000_000).ignored);
        assert!(receiver.packet(&r1, offset + 810_000_000).adopted);
        assert_eq!(receiver.clock(), None);
        assert_eq!(receiver.delay(), 100_000);
    }

    #[test]
    fn before_the_clock_is_known_the_stretch_keeps_the_newest_frames() {
        // The stretch is 4 * 64 = 256 frames; 600 frames arrive before the
        // sender's clock is known.
        let mut receiver: Receiver<4, 8, 4> = receiver();
        for n in 0..60u64 {
            let mut h = header(7, n * 10, 10);
            h.capture = i64::try_from(n).unwrap_or(0) * 1_000;
            let heard = receiver.packet(&h, i64::try_from(n).unwrap_or(0) * 1_000);
            assert_eq!(heard.marked.stored, 10, "packet {n} stored");
            assert_eq!(heard.marked.early, 0, "packet {n} not discarded early");
        }
        assert_eq!(receiver.playhead(), 600 - 256);
        let schedule = receiver
            .schedule()
            .expect("a schedule before the clock is known");
        assert_eq!((schedule.index, schedule.capture), (590, 59_000));
    }

    #[test]
    fn answers_before_the_clock_is_known_are_left_out_and_one_after_it_counts() {
        let offset = 3_600_000_000_000i64;
        let mut receiver: Receiver<4, 8, 4> = receiver();
        let period = 10_000_000i64;
        // The first packet makes the receiver follow timeline 7; the
        // sender's clock is not known yet, so an answer cannot be turned
        // into a delay there and back.
        receiver.packet(&header(7, 0, 480), offset + 100_000);
        let answer = |receiver: &mut Receiver<4, 8, 4>, now: i64| {
            let report = receiver.report().expect("following");
            receiver.reported(report.sequence, now);
            receiver.echo(&Echo {
                stream: 1,
                receiver: 42,
                sequence: report.sequence,
                arrival: now - offset + 140_000,
                departure: now - offset + 140_000,
            });
        };
        for k in 0..20i64 {
            answer(&mut receiver, offset + k * period + 100_000);
        }
        assert_eq!(receiver.delay(), 0);
        // Audio packets make the sender's clock known; one answer then gives
        // the delay.
        stream(&mut receiver, offset, 1, 60);
        assert_eq!(receiver.delay(), 0);
        answer(&mut receiver, offset + 60 * period + 100_000);
        assert_eq!(receiver.delay(), 120_000);
    }

    #[test]
    fn the_path_is_the_smallest_delay_there_and_back_of_the_last_minute() {
        let offset = 3_600_000_000_000i64;
        let mut receiver: Receiver<4, 8, 4> = receiver();
        stream(&mut receiver, offset, 0, 60);
        let period = 10_000_000i64;
        let answer = |receiver: &mut Receiver<4, 8, 4>, now: i64, back: i64| {
            let report = receiver.report().expect("following");
            receiver.reported(report.sequence, now);
            receiver.echo(&Echo {
                stream: 1,
                receiver: 42,
                sequence: report.sequence,
                arrival: now - offset + back,
                departure: now - offset + back,
            });
        };
        // Packets take 100 microseconds from the sender. Reports take 140
        // back at best, and mostly longer.
        let start = offset + 60 * period;
        for (k, back) in (0i64..).zip([900_000, 140_000, 700_000, 2_000_000]) {
            answer(&mut receiver, start + k * period, back);
        }
        assert_eq!(receiver.delay(), 120_000);
        // A minute and more of slow reports, once a second: the fast one is
        // forgotten, and the delay is that of the best report since.
        for k in 1..80i64 {
            answer(
                &mut receiver,
                start + k * 1_000_000_000,
                300_000 + k * 1_000,
            );
        }
        let best = (100_000 + 300_000 + 17 * 1_000) / 2;
        assert!(
            (receiver.delay() - best).abs() <= 8 * 1_000,
            "{}",
            receiver.delay()
        );
    }

    #[test]
    fn adopting_a_new_sender_clock_clears_old_answers_and_departures() {
        // Old sender clock: receiver is 1000 s ahead of sender.
        let old_offset = 1_000_000_000_000i64;
        let mut receiver: Receiver<4, 8, 4> = receiver();
        stream(&mut receiver, old_offset, 0, 60);
        let first_report = receiver.report().expect("following");
        let t_dep = old_offset + 600_000_000;
        receiver.reported(first_report.sequence, t_dep);
        receiver.echo(&Echo {
            stream: 1,
            receiver: 42,
            sequence: first_report.sequence,
            arrival: t_dep - old_offset + 140_000,
            departure: t_dep - old_offset + 140_000,
        });
        assert_eq!(receiver.delay(), 120_000);
        // Also leave an in-flight report from the old clock.
        let old_inflight = receiver.report().expect("following");
        receiver.reported(old_inflight.sequence, t_dep + 10_000_000);

        // Switch to timeline 9 on clock 2 whose clock is 500 s ahead of the old sender.
        let new_offset = 500_000_000_000i64;
        let mut p0 = header(9, 0, 480);
        p0.clock = 2;
        let mut p1 = header(9, 480, 480);
        p1.clock = 2;
        assert!(receiver.packet(&p0, t_dep + 1_000_000_000).ignored);
        assert!(receiver.packet(&p1, t_dep + 1_010_000_000).adopted);
        // Path prior stays until a new-clock echo arrives.
        assert_eq!(receiver.delay(), 120_000);

        // Re-converge on the new sender clock (clock == 2).
        for n in 2..62u64 {
            let mut h = header(9, n * 480, 480);
            h.clock = 2;
            let sent = i64::try_from(n).unwrap_or(0) * 10_000_000 + 500_000_000_000;
            h.capture = sent;
            h.flags = FLAG_STAMPED;
            h.stamped_index = (n - 1) * 480;
            h.stamped_departure = sent - 10_000_000;
            receiver.packet(&h, sent + new_offset + 100_000);
        }
        assert!(receiver.clock().is_some());

        // Delayed echo from the old clock is ignored because departures were cleared.
        receiver.echo(&Echo {
            stream: 1,
            receiver: 42,
            sequence: old_inflight.sequence,
            arrival: t_dep - old_offset + 10_140_000,
            departure: t_dep - old_offset + 10_140_000,
        });
        assert_eq!(receiver.delay(), 120_000);

        // New-clock echo computes the true delay instead of colliding with old answers.
        let new_report = receiver.report().expect("following");
        let new_dep = new_offset + 500_700_000_000;
        receiver.reported(new_report.sequence, new_dep);
        receiver.echo(&Echo {
            stream: 1,
            receiver: 42,
            sequence: new_report.sequence,
            arrival: new_dep - new_offset + 200_000,
            departure: new_dep - new_offset + 200_000,
        });
        assert_eq!(receiver.delay(), 150_000);
    }

    #[test]
    fn sync_snapshot_drives_cycle_and_due_at_without_lower_hull() {
        use crate::kalman::LINE_RUN;
        use crate::player::ModalRegulation;
        use crate::relation::Line;
        use crate::sync::{SyncSnapshot, ZERO_LINE};

        let offset = 3_600_000_000_000i64; // receiver 1 hour ahead of sender
        let mut receiver: Receiver<4, 8, 4> = receiver();
        receiver.enable_sync(ModalRegulation::lipsync(1_000_000, 240));
        // Feed a single unstamped audio packet (no lower-hull samples at all).
        let mut h = header(7, 0, 480);
        h.capture = 0;
        receiver.packet(&h, offset + 100_000);
        // Idle until a valid SyncSnapshot arrives.
        assert_eq!(receiver.due_at(offset + 500_000_000), None);
        assert_eq!(
            receiver.cycle(offset + 500_000_000, 5_000_000, 240).frames,
            0
        );

        let snap = SyncSnapshot {
            valid: true,
            peer_active: false,
            epoch: 1,
            fleet_line: ZERO_LINE,
            common_line: Line {
                time: offset,
                value: -offset,
                rise: 0,
                run: LINE_RUN,
            },
            path_ns: 100_000,
            active_peers: 0,
            common_var_ns2: 25_000_000,
            diff_var_ns2: 0,
        };
        receiver.apply_sync(snap);
        assert_eq!(receiver.delay(), 100_000);
        // At receiver time `offset + 500 ms`, sender time is `500 ms`; with 20 ms
        // level, frame `(500 - 20) * 48 = 23_040` is due.
        let due_pos = receiver.due_at(offset + 500_000_000).expect("due");
        assert_eq!(due_pos.frame, 23_040);
        let plan = receiver.cycle(offset + 500_000_000, 5_000_000, 240);
        assert!(plan.jumped && plan.frames == 240);
        assert_eq!(plan.start.frame, 23_040);
        let next = receiver.cycle(offset + 505_000_000, 5_000_000, 240);
        assert!(!next.jumped);
        assert_eq!(next.start.frame, 23_040 + 240);
    }
}
