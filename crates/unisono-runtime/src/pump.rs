// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! From the core's plan for a cycle to the frames that a device plays.
//!
//! For each cycle of a device the core's receiver says where in the stream
//! the cycle's output frames are taken: a starting position and a step from
//! one output frame to the next. The [`Pump`] does the rest. It takes the
//! frames of the stream that those positions need from the receiver, in
//! order, each exactly once: frames that are held come from the [`Store`],
//! frames that are missing are made by the concealment. It keeps the few
//! frames behind the receiver's playhead that the resampler's filter still
//! reaches back to, and the resampler computes the output from them.
//!
//! A plan can start where the cycle before did not end: the receiver jumps
//! when its position is too far from the schedule. Then the kept frames are
//! dropped. Ahead, the frames in between are skipped. Back, nothing is
//! played twice: frames behind the playhead are never given again, so the
//! pump plays silence until the position has reached the playhead.
//!
//! [`ReceiverPlayback`] ties a receiver, its store and its pump together
//! behind the [`Playback`] interface of an audio device.

use unisono_core::device::Device;
use unisono_core::packet::{Audio, Echo, Report};
use unisono_core::player::{Plan, Regulation};
use unisono_core::receiver::{self, Heard, Receiver};
use unisono_dsp::{Concealment, Filter, Parameters, Position, Resampler, Step, Window};

use crate::audio::Playback;
use crate::store::Store;

/// What a pump did in one cycle.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Played {
    /// Output frames that were taken from the stream.
    pub played: u32,
    /// Output frames of silence, because the plan had no frame for them.
    pub silent: u32,
    /// Frames of the stream that passed the playhead and were held.
    pub held: u32,
    /// Frames of the stream that passed the playhead and were missing, so
    /// that the concealment made them.
    pub concealed: u32,
    /// Frames that the positions of this cycle needed and that could not be
    /// given: behind the playhead after a jump back, or before the first
    /// frame of the timeline. Silence stands for them.
    pub behind: u32,
    /// Frames of the stream that a jump ahead passed over.
    pub skipped: u64,
    /// Whether the cycle did not go on where the one before ended.
    pub jumped: bool,
}

/// What a pump did in all its cycles so far.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Totals {
    /// The number of cycles.
    pub cycles: u64,
    /// The number of cycles that did not go on where the one before ended.
    pub jumps: u64,
    /// See [`Played::played`].
    pub played: u64,
    /// See [`Played::silent`].
    pub silent: u64,
    /// See [`Played::held`].
    pub held: u64,
    /// See [`Played::concealed`].
    pub concealed: u64,
    /// See [`Played::behind`].
    pub behind: u64,
    /// See [`Played::skipped`].
    pub skipped: u64,
}

impl Totals {
    /// Adds what one cycle did. The counts wrap around at their largest
    /// value.
    pub fn add(&mut self, cycle: &Played) {
        self.cycles = self.cycles.wrapping_add(1);
        self.jumps = self.jumps.wrapping_add(u64::from(cycle.jumped));
        self.played = self.played.wrapping_add(u64::from(cycle.played));
        self.silent = self.silent.wrapping_add(u64::from(cycle.silent));
        self.held = self.held.wrapping_add(u64::from(cycle.held));
        self.concealed = self.concealed.wrapping_add(u64::from(cycle.concealed));
        self.behind = self.behind.wrapping_add(u64::from(cycle.behind));
        self.skipped = self.skipped.wrapping_add(cycle.skipped);
    }
}

/// `count` as a 32-bit number, or the largest one.
fn narrow(count: usize) -> u32 {
    u32::try_from(count).unwrap_or(u32::MAX)
}

/// Turns the core's plan for a cycle into output frames.
///
/// It allocates when it is made and not afterwards.
#[derive(Clone, Debug)]
pub struct Pump {
    channels: usize,
    resampler: Resampler,
    concealment: Concealment,
    /// The most output frames that are computed in one go.
    block: usize,
    /// The number of frames that `window` has room for.
    capacity: usize,
    /// Consecutive frames of the stream as they left the concealment. The
    /// frame at place `i` has the index `first + i - before`, where `before`
    /// is the number of frames that the filter reaches back: counting from
    /// `before` on keeps the places of the frames before index 0, which the
    /// first positions of a timeline need, from being negative.
    window: Box<[f32]>,
    first: u64,
    length: usize,
    /// One frame that is written and not played.
    scratch: Box<[f32]>,
    /// Where the next output frame would come from if playback stopped abruptly
    /// and needs to fade out smoothly through the resampler and concealment.
    tail: Option<(Position, Step)>,
    /// How many consecutive silent frames have been appended to `window` while
    /// draining `tail`.
    tail_silent: usize,
}

impl Pump {
    /// A pump for frames of `channels` samples that interpolates with
    /// `filter`, conceals with the sizes `concealment`, and computes at most
    /// `block` output frames in one go. `block` is brought into 1 to 65,536;
    /// it changes how the work is cut up, and not what comes out.
    #[must_use]
    pub fn new(filter: Filter, channels: usize, concealment: Parameters, block: usize) -> Pump {
        let block = block.clamp(1, 1 << 16);
        // A block of output frames advances by less than `block * (1 +
        // 2^-8)` frames, and each position needs `taps` frames around it.
        let capacity = block + block / 128 + filter.taps() + 2;
        Pump {
            channels,
            resampler: Resampler::new(filter, channels),
            concealment: Concealment::new(channels, concealment),
            block,
            capacity,
            window: vec![0.0; capacity.saturating_mul(channels)].into_boxed_slice(),
            first: 0,
            length: 0,
            scratch: vec![0.0; channels].into_boxed_slice(),
            tail: None,
            tail_silent: 0,
        }
    }

    /// The filter that gives the value between frames.
    #[must_use]
    pub fn filter(&self) -> &Filter {
        self.resampler.filter()
    }

    /// The number of samples in a frame.
    #[must_use]
    pub fn channels(&self) -> usize {
        self.channels
    }

    /// Fills `output`, the frames of one cycle of a device, as `plan` says:
    /// output frame `i` is the stream at the position `i` steps after the
    /// plan's start, for as many frames as the plan has. Any remaining frames
    /// fade out smoothly through the concealment to silence.
    ///
    /// The frames of the stream that this needs and that have not passed the
    /// playhead of `receiver` are taken from it, the held ones out of
    /// `store`, which must be the store that the receiver's packets were
    /// written to.
    pub fn play<const N: usize, const M: usize, const K: usize>(
        &mut self,
        receiver: &mut Receiver<N, M, K>,
        store: &Store,
        plan: &Plan,
        output: &mut [f32],
    ) -> Played {
        let mut done = Played::default();
        if self.channels == 0 {
            return done;
        }
        let cycle = output.len() / self.channels;
        let wanted = usize::try_from(plan.frames)
            .unwrap_or(usize::MAX)
            .min(cycle);
        self.concealment.cycle_begins();
        let start = plan.start;
        let step = plan.step;
        if plan.jumped && wanted > 0 {
            self.jump();
            done.jumped = true;
        }
        let mut written = 0;
        while written < wanted {
            let frames = (wanted - written).min(self.block);
            let Some(at) = start.advance(step, written as u64) else {
                break;
            };
            let from = written * self.channels;
            let Some(block) = output.get_mut(from..from + frames * self.channels) else {
                break;
            };
            let produced = self.block(receiver, store, at, step, block, &mut done);
            if produced > 0 {
                self.tail = at.advance(step, produced as u64).map(|next| (next, step));
                self.tail_silent = 0;
            }
            written += produced;
            if produced < frames {
                break;
            }
        }
        if let Some(rest) = output.get_mut(written * self.channels..)
            && !rest.is_empty()
        {
            self.fade_tail(rest);
        }
        done.played = narrow(written);
        done.silent = narrow(cycle - written);
        done
    }

    /// Forgets the kept frames, and lets what was playing fade out under
    /// what comes next.
    fn jump(&mut self) {
        self.length = 0;
        self.tail = None;
        self.tail_silent = 0;
        // A frame that is made and not played begins a gap for the
        // concealment, so that the frames after it fade in.
        self.concealment.fill(&mut self.scratch);
    }

    /// Fades out any audio still trailing from the previous active cycle
    /// through the resampler and concealment, then writes silence once the
    /// filter window has drained to zero.
    fn fade_tail(&mut self, output: &mut [f32]) {
        let frames = output.len() / self.channels;
        let whole = frames * self.channels;
        if let Some(leftover) = output.get_mut(whole..) {
            leftover.fill(0.0);
        }
        if frames == 0 {
            return;
        }
        if self.concealment.fade_out().frames() == 0 || self.tail.is_none() {
            self.tail = None;
            self.tail_silent = 0;
            self.length = 0;
            if !self.concealment.is_silent() {
                self.concealment.fill(&mut self.scratch);
            }
            if let Some(target) = output.get_mut(..whole) {
                target.fill(0.0);
            }
            return;
        }
        let mut written = 0;
        while written < frames {
            let Some((at, step)) = self.tail else {
                if let Some(rem) = output.get_mut(written * self.channels..whole) {
                    rem.fill(0.0);
                }
                break;
            };
            let chunk_frames = (frames - written).min(self.block);
            let from = written * self.channels;
            let Some(block) = output.get_mut(from..from + chunk_frames * self.channels) else {
                break;
            };
            let produced = self.fade_tail_block(at, step, block);
            written += produced;
            if produced < chunk_frames {
                self.tail = None;
                self.tail_silent = 0;
                self.length = 0;
                if let Some(rem) = output.get_mut(written * self.channels..whole) {
                    rem.fill(0.0);
                }
                break;
            }
        }
    }

    /// Produces one block of fade-out tail frames at `(at, step)` using only
    /// frames already in `window` and concealment continuation frames.
    fn fade_tail_block(&mut self, at: Position, step: Step, output: &mut [f32]) -> usize {
        let frames = output.len() / self.channels;
        if frames == 0 {
            return 0;
        }
        let before = self.resampler.filter().before() as u64;
        let taps = self.resampler.filter().taps() as u64;
        let Some(last) = at.advance(step, frames as u64 - 1) else {
            return 0;
        };
        let from = at.frame();
        let (Some(to), Some(shifted)) = (
            last.frame().checked_add(taps - 1),
            at.frame().checked_add(before),
        ) else {
            return 0;
        };
        if to - from >= self.capacity as u64 {
            return 0;
        }
        self.keep_from(from);
        while self.length < self.capacity {
            let Some(next) = self.first.checked_add(self.length as u64) else {
                break;
            };
            if next > to {
                break;
            }
            let room = self.capacity - self.length;
            let count = usize::try_from(to - next)
                .unwrap_or(usize::MAX)
                .saturating_add(1)
                .min(room);
            let start_sample = self.length * self.channels;
            let Some(slot) = self
                .window
                .get_mut(start_sample..start_sample + count * self.channels)
            else {
                break;
            };
            let already_silent = self.concealment.is_silent();
            self.concealment.fill(slot);
            if already_silent {
                self.tail_silent = self.tail_silent.saturating_add(count);
            }
            self.length += count;
        }
        let window = Window {
            first: self.first,
            samples: self
                .window
                .get(..self.length * self.channels)
                .unwrap_or(&[]),
        };
        let start = Position::new(shifted, at.fraction());
        let produced = self.resampler.process(window, start, step, output).frames;
        if self.tail_silent >= self.resampler.filter().taps() {
            self.tail = None;
            self.tail_silent = 0;
            self.length = 0;
        } else {
            self.tail = at.advance(step, produced as u64).map(|next| (next, step));
        }
        produced
    }

    /// Computes the output frames in `output` at the positions `at`, `at +
    /// step` and so on, and returns how many it computed: all of them,
    /// unless a position lies beyond the last index.
    fn block<const N: usize, const M: usize, const K: usize>(
        &mut self,
        receiver: &mut Receiver<N, M, K>,
        store: &Store,
        at: Position,
        step: Step,
        output: &mut [f32],
        done: &mut Played,
    ) -> usize {
        let frames = output.len() / self.channels;
        if frames == 0 {
            return 0;
        }
        let before = self.resampler.filter().before() as u64;
        let taps = self.resampler.filter().taps() as u64;
        // Places are counted from `before` on, so the position `at` reads
        // the places from `at.frame()` to `at.frame() + taps - 1`.
        let Some(last) = at.advance(step, frames as u64 - 1) else {
            return 0;
        };
        let from = at.frame();
        let (Some(to), Some(shifted)) = (
            last.frame().checked_add(taps - 1),
            at.frame().checked_add(before),
        ) else {
            return 0;
        };
        if to - from >= self.capacity as u64 {
            return 0;
        }
        self.keep_from(from);
        self.fetch(receiver, store, to, done);
        let window = Window {
            first: self.first,
            samples: self
                .window
                .get(..self.length * self.channels)
                .unwrap_or(&[]),
        };
        let start = Position::new(shifted, at.fraction());
        self.resampler.process(window, start, step, output).frames
    }

    /// Drops the kept frames before the place `from`, or all of them when
    /// `from` is not among them or just after them.
    fn keep_from(&mut self, from: u64) {
        let dropped = from
            .checked_sub(self.first)
            .and_then(|dropped| usize::try_from(dropped).ok())
            .filter(|dropped| *dropped <= self.length);
        match dropped {
            Some(dropped) => {
                self.window
                    .copy_within(dropped * self.channels..self.length * self.channels, 0);
                self.length -= dropped;
            }
            None => self.length = 0,
        }
        self.first = from;
    }

    /// Extends the kept frames up to the place `to`, with frames from the
    /// receiver where the playhead has not passed them and with concealment
    /// where it has.
    fn fetch<const N: usize, const M: usize, const K: usize>(
        &mut self,
        receiver: &mut Receiver<N, M, K>,
        store: &Store,
        to: u64,
        done: &mut Played,
    ) {
        let before = self.resampler.filter().before() as u64;
        while self.length < self.capacity {
            let Some(next) = self.first.checked_add(self.length as u64) else {
                return;
            };
            if next > to {
                return;
            }
            let room = self.capacity - self.length;
            let wanted = usize::try_from(to - next)
                .unwrap_or(usize::MAX)
                .saturating_add(1)
                .min(room);
            let from = self.length * self.channels;
            let Some(tail) = self.window.get_mut(from..from + wanted * self.channels) else {
                return;
            };
            // How many of the wanted frames cannot be given: those before
            // the first frame of the timeline, and those behind the playhead.
            let playhead = receiver.playhead();
            let missing = match next.checked_sub(before) {
                None => before - next,
                Some(index) => playhead.saturating_sub(index),
            };
            if missing > 0 {
                let count = usize::try_from(missing).unwrap_or(usize::MAX).min(wanted);
                if let Some(silence) = tail.get_mut(..count * self.channels) {
                    self.concealment.fill(silence);
                }
                done.behind = done.behind.saturating_add(narrow(count));
                self.length += count;
                continue;
            }
            let index = next - before;
            if index > playhead {
                done.skipped = done.skipped.saturating_add(receiver.skip(index));
            }
            let segment = receiver.take(narrow(wanted));
            let count = usize::try_from(segment.frames)
                .unwrap_or(usize::MAX)
                .min(wanted);
            if count == 0 || segment.first != index {
                // No timeline is followed, so there is nothing to take.
                self.concealment.fill(tail);
                done.behind = done.behind.saturating_add(narrow(wanted));
                self.length += wanted;
                continue;
            }
            let Some(run) = tail.get_mut(..count * self.channels) else {
                return;
            };
            if segment.held {
                store.read(segment.first, run);
                self.concealment.pass(run);
                done.held = done.held.saturating_add(narrow(count));
            } else {
                self.concealment.fill(run);
                done.concealed = done.concealed.saturating_add(narrow(count));
            }
            self.length += count;
        }
    }
}

/// What a receiver that plays on a device is set up with.
#[derive(Clone, Copy, Debug)]
pub struct Settings {
    /// The stream identifier that this receiver accepts.
    pub stream: u16,
    /// Frames per second of the stream and of the device.
    pub rate: u32,
    /// The number of samples in a frame.
    pub channels: u8,
    /// A number that tells this receiver from the others of the stream.
    pub identity: u64,
    /// After how many nanoseconds without a packet of the timeline it
    /// follows the receiver takes up another, and after how long without a
    /// frame at or ahead of its playhead it starts anew.
    pub silence: i64,
    /// The largest slope of the receiver's estimate of the sender's clock,
    /// in nanoseconds per second.
    pub slope_limit: i64,
    /// The settings of the receiver's regulator.
    pub regulation: Regulation,
    /// The sizes of the concealment.
    pub concealment: Parameters,
    /// The most output frames that are computed in one go.
    pub block: usize,
    /// How far the rate of the line fitted to the device's reports may be
    /// from the nominal rate for the line to be used, in parts per billion.
    /// A line further off comes from too few reports or from reports that
    /// are wrong, and the nominal rate is used in its place.
    pub device_range: u32,
}

/// A receiver, the samples it holds and its pump, as what a playback device
/// plays.
///
/// Packets are handed to it as they arrive, and the device asks it for the
/// frames of each cycle. Both happen on one thread, or one at a time.
///
/// The receiver holds up to `64 * N` frames, remembers `M` samples of the
/// sender's clock and keeps the arrivals of `K` packets.
pub struct ReceiverPlayback<const N: usize, const M: usize, const K: usize, const W: usize> {
    receiver: Receiver<N, M, K>,
    store: Store,
    pump: Pump,
    /// The line through the last `W` reports of the device.
    device: Device<W>,
    /// How far its rate may be from the nominal one, in parts per billion.
    device_range: u32,
    /// Sub-nanosecond duration remainder carried between cycles, in units of
    /// 2^-16 nanosecond.
    carried: i64,
    rate: u32,
    channels: u8,
    last: Played,
    totals: Totals,
}

impl<const N: usize, const M: usize, const K: usize, const W: usize> ReceiverPlayback<N, M, K, W> {
    /// A receiver that follows no timeline yet.
    #[must_use]
    pub fn new(settings: &Settings) -> Self {
        let channels = usize::from(settings.channels);
        ReceiverPlayback {
            receiver: Receiver::new(receiver::Settings {
                stream: settings.stream,
                identity: settings.identity,
                silence: settings.silence,
                limit: settings.slope_limit,
                regulation: settings.regulation,
            }),
            store: Store::for_stretch(N, channels),
            pump: Pump::new(
                Filter::for_rate(settings.rate),
                channels,
                settings.concealment,
                settings.block,
            ),
            device: Device::new(settings.rate),
            device_range: settings.device_range,
            carried: 0,
            rate: settings.rate,
            channels: settings.channels,
            last: Played::default(),
            totals: Totals::default(),
        }
    }

    /// The receiver of the core.
    #[must_use]
    pub fn receiver(&self) -> &Receiver<N, M, K> {
        &self.receiver
    }

    /// Sets the receiver's estimate of the smallest delay of a packet from
    /// the sender, in nanoseconds.
    pub fn path(&mut self, path: i64) {
        self.receiver.path(path);
    }

    /// Makes the next report to send back to the sender, or `None` when no
    /// timeline is followed yet.
    pub fn report(&mut self) -> Option<Report> {
        self.receiver.report()
    }

    /// Records the reading of the host's clock when report `sequence` left
    /// the host.
    pub fn reported(&mut self, sequence: u64, departure: i64) {
        self.receiver.reported(sequence, departure);
    }

    /// Takes in the sender's echo of a report to update the path-delay
    /// estimate.
    pub fn echo(&mut self, echo: &Echo) {
        self.receiver.echo(echo);
    }

    /// The number of frames after a position that the device's output at
    /// that position needs: a frame must have arrived this many frames
    /// before it is due, and the cycle's lead besides.
    #[must_use]
    pub fn reach(&self) -> usize {
        self.pump.filter().ahead()
    }

    /// Takes in an audio packet: its header, its samples as the packet
    /// carries them, and the reading of the host's clock at its arrival.
    ///
    /// Returns what the receiver did with it, or `None` when the packet is
    /// not for this receiver: another rate, another number of channels, or
    /// samples that are not as many as the header says.
    pub fn packet(&mut self, header: &Audio, payload: &[u8], arrival: i64) -> Option<Heard> {
        let samples = usize::from(header.frames)
            .checked_mul(usize::from(header.channels))?
            .checked_mul(header.format.bytes())?;
        if header.rate != self.rate || header.channels != self.channels || payload.len() != samples
        {
            return None;
        }
        let heard = self.receiver.packet(header, arrival);
        if !heard.ignored {
            let receiver = &self.receiver;
            self.store
                .write_packet(header.index, header.format, payload, |index| {
                    receiver.covers(index)
                });
        }
        Some(heard)
    }

    /// What the last cycle did.
    #[must_use]
    pub fn last(&self) -> Played {
        self.last
    }

    /// What all cycles so far did.
    #[must_use]
    pub fn totals(&self) -> Totals {
        self.totals
    }

    /// Updates the device clock line with this cycle's `(position, time)`
    /// report and returns the fitted `(start, duration)` in nanoseconds.
    fn step_device(&mut self, position: u64, time: i64, frames: u32) -> (i64, i64) {
        self.device.observe(position, time);
        let nominal_q16 = (i128::from(frames) << 16) * 1_000_000_000 / i128::from(self.rate.max(1));
        let (fitted_start, measured_q16) = self
            .device
            .when_cycle(position, frames)
            .map_or((time, nominal_q16), |(s, d)| (s, i128::from(d)));
        let usable = self.device.kept() > 1
            && measured_q16 > 0
            && (measured_q16 - nominal_q16).abs() * 1_000_000_000
                <= nominal_q16 * i128::from(self.device_range);
        let duration_q16 = if usable {
            measured_q16
        } else {
            self.carried = 0;
            nominal_q16
        };
        let exact = duration_q16 + i128::from(self.carried);
        #[allow(clippy::cast_possible_truncation)] // masked to 16 bits
        {
            self.carried = (exact & 0xffff) as i64;
        }
        let duration = i64::try_from(exact >> 16).unwrap_or(i64::MAX);
        let start = if usable { fitted_start } else { time };
        (start, duration)
    }
}

impl<const N: usize, const M: usize, const K: usize, const W: usize> Playback
    for ReceiverPlayback<N, M, K, W>
{
    fn channels(&self) -> usize {
        usize::from(self.channels)
    }

    fn cycle(&mut self, frames: &mut [f32], position: u64, time: i64) {
        let count = narrow(frames.len() / usize::from(self.channels).max(1));
        let (start, duration) = self.step_device(position, time, count);
        let plan = self.receiver.cycle(start, duration, count);
        self.last = self
            .pump
            .play(&mut self.receiver, &self.store, &plan, frames);
        self.totals.add(&self.last);
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::player::Regulation;
    use unisono_core::timing;
    use unisono_dsp::{Parameters, Position, Step};

    use super::{ReceiverPlayback, Settings};

    fn test_playback(rate: u32) -> ReceiverPlayback<16, 16, 4, 64> {
        ReceiverPlayback::new(&Settings {
            stream: 1,
            rate,
            channels: 2,
            identity: 1,
            silence: 1_000_000_000,
            slope_limit: 200_000,
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
            concealment: Parameters::for_rate(rate),
            block: 256,
            device_range: 10_000_000,
        })
    }

    /// The pump computes positions with the resampler's arithmetic and the
    /// core plans with its own. If the two did not agree to the last unit, a
    /// cycle would end where the next does not begin.
    #[test]
    fn the_resampler_and_the_core_advance_a_position_alike() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut draw = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let largest = Step::LARGEST_OFFSET;
        for round in 0..20_000 {
            let frame = draw() >> (draw() % 40);
            let fraction = match round % 4 {
                0 => 0,
                1 => u64::MAX,
                _ => draw(),
            };
            let offset = match round % 5 {
                0 => largest,
                1 => -largest,
                2 => 0,
                _ => i64::try_from(draw() % (2 * largest.unsigned_abs())).unwrap_or(0) - largest,
            };
            let frames = u32::try_from(draw() % 100_000).unwrap_or(0);
            let core = timing::advance(timing::Position { frame, fraction }, frames, offset);
            let step = Step::new(offset).expect("within the largest offset");
            let resampler = Position::new(frame, fraction)
                .advance(step, u64::from(frames))
                .expect("far from the largest position");
            assert_eq!(
                (core.frame, core.fraction),
                (resampler.frame(), resampler.fraction()),
                "frame {frame}, fraction {fraction}, offset {offset}, {frames} frames"
            );
        }
    }

    /// A device at 50,000 frames a second, whose frames last 20,000
    /// nanoseconds exactly, running a thousandth fast: 250 frames take
    /// 4,995,004.995 ns.
    #[test]
    fn the_length_of_a_cycle_follows_the_device_s_reports() {
        let mut playback = test_playback(50_000);
        let at =
            |position: u64| i64::try_from(u128::from(position) * 20_000_000 / 1_001).unwrap_or(0);
        // Without an earlier report, the nominal length.
        assert_eq!(playback.step_device(0, at(0), 250), (0, 5_000_000));
        let mut sum = 0;
        for cycle in 1..=1_000u64 {
            let (_, duration) = playback.step_device(cycle * 250, at(cycle * 250), 250);
            assert!(
                (duration - 4_995_005).abs() <= 1,
                "cycle {cycle}: {duration}"
            );
            sum += duration;
        }
        // The lengths are whole nanoseconds, and what one leaves out the
        // next ones make up: a thousand of them are a thousand cycles long,
        // to within what the rounding of the reports allows.
        assert!((sum - 4_995_004_995).abs() <= 40, "sum {sum}");
    }

    /// After a clock jump across a break in the device's count, the reports
    /// before it are dropped.
    #[test]
    fn a_break_in_the_count_starts_the_reports_anew() {
        let mut playback = test_playback(50_000);
        for cycle in 0..10u64 {
            playback.step_device(
                cycle * 250,
                i64::try_from(cycle).unwrap_or(0) * 5_000_000,
                250,
            );
        }
        // The device left out a second of frames and half a second of time.
        assert_eq!(
            playback.step_device(52_500, 550_000_000, 250),
            (550_000_000, 5_000_000)
        );
        assert_eq!(
            playback.step_device(52_750, 555_000_000, 250),
            (555_000_000, 5_000_000)
        );
    }

    /// Reports that give a rate far from the nominal one are not believed.
    #[test]
    fn a_rate_far_from_the_nominal_one_is_not_taken() {
        let mut playback = test_playback(50_000);
        playback.step_device(0, 0, 250);
        // Twice as fast as nominal.
        assert_eq!(
            playback.step_device(250, 2_500_000, 250),
            (2_500_000, 5_000_000)
        );
        // A time that runs backwards.
        assert_eq!(
            playback.step_device(500, 1_000_000, 250),
            (1_000_000, 5_000_000)
        );
    }
}
