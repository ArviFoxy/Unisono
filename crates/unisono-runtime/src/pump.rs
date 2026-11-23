// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Audio playback pipeline translating core playback plans into resampled PCM.
//!
//! Each device cycle, `unisono_core::receiver::Receiver` returns a [`Plan`]
//! giving the starting fractional stream position and per-sample step.
//! [`Pump`] advances the receiver playhead strictly monotonically, pulls
//! available frames from [`Store`], synthesizes missing frames via
//! [`Concealment`], maintains the FIR resampler lookbehind window, and renders
//! output samples via [`Resampler`].
//!
//! On a discontinuous jump (`plan.jumped`), the resampler window is flushed:
//! jumping forward skips intervening frames; jumping backward outputs silence
//! until the position catches up to the monotonic playhead so frames are never
//! replayed twice.
//!
//! [`ReceiverPlayback`] wraps `Receiver`, `Store`, and `Pump` behind the
//! real-time [`Playback`] trait.

use unisono_core::device::Device;
use unisono_core::needs::Needs;
use unisono_core::packet::{Audio, Echo, RECENT, Recent, Report};
use unisono_core::player::{ModalRegulation, Plan, Regulation};
use unisono_core::receiver::{self, Heard, Receiver};
use unisono_core::sync::SyncSnapshot;
use unisono_core::timing;
use unisono_dsp::{Concealment, Filter, Parameters, Position, Resampler, Step, Window};

use crate::InvalidSettings;
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

/// The revisions of the schedule from cycle to cycle, added up. A revision
/// is how far the position that is due at the start of a cycle lies from
/// where the cycle before expected it: what the receiver's estimates of the
/// clocks changed by in between. The regulator's law is the best when a
/// revision cannot be foreseen from those before it, and then the products
/// of successive revisions add up to nothing against their squares.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Revisions {
    /// The number of revisions.
    pub count: u64,
    /// The sum of their squares, in square frames.
    pub squares: f64,
    /// The sum of the products of each with the one before it, in square
    /// frames.
    pub products: f64,
}

impl Revisions {
    /// Adds the revision `revision`, in frames, that follows the revision
    /// `before`, if one does.
    fn add(&mut self, revision: f64, before: Option<f64>) {
        self.count = self.count.wrapping_add(1);
        self.squares += revision * revision;
        if let Some(before) = before {
            self.products += revision * before;
        }
    }
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

/// Whether the pump's resampling window currently holds stream frames or
/// synthetic fade-out frames.
#[derive(Clone, Copy, Debug)]
enum State {
    /// No audio is trailing from a previous cycle; `window` is empty.
    Idle,
    /// Actively playing stream frames; `window` holds stream frames and
    /// `(next, step)` is where a fade-out would continue if playback stops.
    Playing { next: Position, step: Step },
    /// Draining a fade-out tail after playback paused; `window` holds any
    /// remaining real stream frames strictly before `real_end` followed by
    /// synthetic concealment frames at `>= real_end`. Resuming without a jump
    /// truncates `window` back to `real_end` so real frames are kept while
    /// synthetic frames are discarded.
    Fading {
        next: Position,
        step: Step,
        silent: usize,
        real_end: u64,
    },
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
    /// Playback / fade-out state owning the provenance of `window`.
    state: State,
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
            state: State::Idle,
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
        if wanted > 0 {
            if plan.jumped {
                self.jump();
                done.jumped = true;
            } else if let State::Fading { real_end, .. } = self.state {
                // Keep real stream frames still in `window` (`< real_end`)
                // while discarding synthetic fade-out frames appended after
                // them so `fetch` reads newly arrived stream frames.
                let real_len = usize::try_from(real_end.saturating_sub(self.first))
                    .unwrap_or(self.length)
                    .min(self.length);
                self.length = real_len;
                self.state = State::Idle;
            }
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
                self.state = at
                    .advance(step, produced as u64)
                    .map_or(State::Idle, |next| State::Playing { next, step });
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
        self.state = State::Idle;
        // A frame that is made and not played begins a gap for the
        // concealment, so that the frames after it fade in.
        self.concealment.fill(&mut self.scratch);
    }

    /// Computes the `(from, to, shifted)` window range for `frames` output
    /// frames starting at `at` with step `step`, returning `None` if the
    /// range would overflow or exceed `self.capacity`.
    fn block_range(&self, at: Position, step: Step, frames: usize) -> Option<(u64, u64, u64)> {
        if frames == 0 {
            return None;
        }
        let before = self.resampler.filter().before() as u64;
        let taps = self.resampler.filter().taps() as u64;
        // Places are counted from `before` on, so the position `at` reads
        // the places from `at.frame()` to `at.frame() + taps - 1`.
        let last = at.advance(step, frames as u64 - 1)?;
        let from = at.frame();
        let to = last.frame().checked_add(taps - 1)?;
        let shifted = at.frame().checked_add(before)?;
        (to - from < self.capacity as u64).then_some((from, to, shifted))
    }

    /// Resamples `output` from the current `self.window` starting at
    /// `Position::new(shifted, at.fraction())`.
    fn resample_window(
        &mut self,
        shifted: u64,
        at: Position,
        step: Step,
        output: &mut [f32],
    ) -> usize {
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

    /// Fades out any audio still trailing from the previous active cycle
    /// through the resampler and concealment, then writes silence once the
    /// filter window has drained to zero.
    fn fade_tail(&mut self, output: &mut [f32]) {
        let frames = output.len().checked_div(self.channels).unwrap_or(0);
        let whole = frames * self.channels;
        if let Some(leftover) = output.get_mut(whole..) {
            leftover.fill(0.0);
        }
        if frames == 0 {
            return;
        }
        if let State::Playing { next, step } = self.state {
            self.state = State::Fading {
                next,
                step,
                silent: 0,
                real_end: self.first.saturating_add(self.length as u64),
            };
        }
        if self.concealment.fade_out().frames() == 0 || matches!(self.state, State::Idle) {
            self.state = State::Idle;
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
            let State::Fading {
                next: at,
                step,
                silent,
                real_end,
            } = self.state
            else {
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
            let produced = self.fade_tail_block(at, step, silent, real_end, block);
            written += produced;
            if produced < chunk_frames {
                self.state = State::Idle;
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
    fn fade_tail_block(
        &mut self,
        at: Position,
        step: Step,
        mut silent: usize,
        real_end: u64,
        output: &mut [f32],
    ) -> usize {
        let frames = output.len().checked_div(self.channels).unwrap_or(0);
        let Some((from, to, shifted)) = self.block_range(at, step, frames) else {
            return 0;
        };
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
                silent = silent.saturating_add(count);
            }
            self.length += count;
        }
        let produced = self.resample_window(shifted, at, step, output);
        if silent >= self.resampler.filter().taps() {
            self.state = State::Idle;
            self.length = 0;
        } else {
            self.state = at
                .advance(step, produced as u64)
                .map_or(State::Idle, |next| State::Fading {
                    next,
                    step,
                    silent,
                    real_end,
                });
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
        let frames = output.len().checked_div(self.channels).unwrap_or(0);
        let Some((from, to, shifted)) = self.block_range(at, step, frames) else {
            return 0;
        };
        self.keep_from(from);
        self.fetch(receiver, store, to, done);
        self.resample_window(shifted, at, step, output)
    }

    /// Drops the kept frames before the place `from`, or all of them when
    /// `from` is not among them or just after them.
    fn keep_from(&mut self, from: u64) {
        let dropped = from
            .checked_sub(self.first)
            .and_then(|dropped| usize::try_from(dropped).ok())
            .filter(|dropped| *dropped <= self.length);
        // The kept samples are within the window, and those that are kept on
        // within them; the comparisons say so to the compiler as well, which
        // then leaves no way to fail in the copy.
        let kept = dropped.and_then(|dropped| {
            let start = dropped.checked_mul(self.channels)?;
            let end = self.length.checked_mul(self.channels)?;
            (start <= end && end <= self.window.len()).then_some((dropped, start, end))
        });
        match kept {
            Some((dropped, start, end)) => {
                self.window.copy_within(start..end, 0);
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

/// Shipped receiver silence timeout before adopting a new timeline, in ns.
pub const SHIPPED_SILENCE_NS: i64 = 1_000_000_000;

/// Shipped receiver clock-estimator slope limit, in ns/s.
pub const SHIPPED_SLOPE_LIMIT: i64 = 200_000;

/// Shipped single-mode regulator gain in Q16 (`4.0 / s`).
pub const SHIPPED_REGULATION_GAIN: u32 = 4 << 16;

/// Shipped playback pace limit, in ppb (`1000 ppm`).
pub const SHIPPED_REGULATION_LIMIT: u32 = 1_000_000;

/// Shipped pump resampling sub-block size, in output frames.
pub const SHIPPED_BLOCK: usize = 256;

/// Shipped accepted audio-device clock-rate deviation, in ppb (`1%`).
pub const SHIPPED_DEVICE_RANGE: u32 = 10_000_000;

/// Shipped default playback request lead, in nanoseconds (`4 ms`).
pub const SHIPPED_LEAD_NS: i64 = 4_000_000;

/// Shipped receiver playback dimensions: 16,384 held frames (`256 * 64`),
/// 64 lower-hull clock samples, 8 packet-arrival slots, and 64 device reports.
pub type ShippedPlayback = ReceiverPlayback<256, 64, 8, 64>;

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
    /// The settings of the receiver's single-mode regulator (used in legacy
    /// lower-hull mode and as the fallback when `modal_regulation` is `None`).
    pub regulation: Regulation,
    /// Optional two-mode (`ModalPlayer`) regulation used when [`SyncSnapshot`]
    /// clock estimation is enabled (`--sync peer`, default). `None` selects the
    /// legacy one-way lower-hull clock estimator (`--sync hull`).
    pub modal_regulation: Option<ModalRegulation>,
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

impl Settings {
    /// Builds the shipped validated receiver [`Settings`] shared by the CLI, C
    /// library, and simulator.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidSettings`] when any field violates [`Settings::validate`].
    pub fn shipped(
        stream: u16,
        rate: u32,
        channels: u8,
        identity: u64,
        modal_regulation: Option<ModalRegulation>,
    ) -> Result<Settings, InvalidSettings> {
        let settings = Settings {
            stream,
            rate,
            channels,
            identity,
            silence: SHIPPED_SILENCE_NS,
            slope_limit: SHIPPED_SLOPE_LIMIT,
            regulation: Regulation {
                gain: SHIPPED_REGULATION_GAIN,
                limit: SHIPPED_REGULATION_LIMIT,
                jump: (rate / 200).max(1),
            },
            modal_regulation,
            concealment: Parameters::for_rate(rate),
            block: SHIPPED_BLOCK,
            device_range: SHIPPED_DEVICE_RANGE,
        };
        settings.validate()?;
        Ok(settings)
    }

    /// Validates that rate, channels, silence timeout, clock slope limit,
    /// regulator jump threshold, and block size satisfy runtime invariants.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidSettings`] when any parameter is out of range.
    pub fn validate(&self) -> Result<(), InvalidSettings> {
        if self.rate == 0 {
            return Err(InvalidSettings::new("sample rate must be positive"));
        }
        if self.channels == 0 {
            return Err(InvalidSettings::new("channel count must be positive"));
        }
        if self.silence < 0 {
            return Err(InvalidSettings::new("silence timeout must be non-negative"));
        }
        if self.slope_limit < 0 || self.slope_limit >= 1_000_000_000 {
            return Err(InvalidSettings::new(
                "clock slope limit must be in 0..1_000_000_000 ns/s",
            ));
        }
        if self.regulation.jump == 0 {
            return Err(InvalidSettings::new(
                "regulator jump threshold must be at least 1 frame",
            ));
        }
        if let Some(modal) = self.modal_regulation
            && modal.jump == 0
        {
            return Err(InvalidSettings::new(
                "modal regulator jump threshold must be at least 1 frame",
            ));
        }
        if self.block == 0 {
            return Err(InvalidSettings::new("pump block size must be at least 1"));
        }
        Ok(())
    }
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
    /// The largest need of each of the last stretches of the followed
    /// timeline.
    needs: Needs<RECENT>,
    /// The line through the last `W` reports of the device.
    device: Device<W>,
    /// How far its rate may be from the nominal one, in parts per billion.
    device_range: u32,
    /// Explicit fixed path delay override (`--path`), if configured.
    told_path: Option<i64>,
    /// Whether at least one playback cycle has played frames on the current
    /// timeline (so `playhead` tracks the schedule rather than the initial
    /// adoption index).
    timeline_played: bool,
    revisions: Revisions,
    /// The position that the cycle before expected to be due at the start
    /// of this one.
    expected: Option<timing::Position>,
    /// The revision at the start of the cycle before, in frames.
    revised: Option<f64>,
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
        let mut receiver = Receiver::new(receiver::Settings {
            stream: settings.stream,
            identity: settings.identity,
            silence: settings.silence,
            limit: settings.slope_limit,
            regulation: settings.regulation,
        });
        if let Some(modal) = settings.modal_regulation {
            receiver.enable_sync(modal);
        }
        ReceiverPlayback {
            receiver,
            store: Store::for_stretch(N, channels),
            pump: Pump::new(
                Filter::for_rate(settings.rate),
                channels,
                settings.concealment,
                settings.block,
            ),
            needs: Needs::new(),
            device: Device::new(settings.rate),
            device_range: settings.device_range,
            told_path: None,
            timeline_played: false,
            revisions: Revisions::default(),
            expected: None,
            revised: None,
            carried: 0,
            rate: settings.rate,
            channels: settings.channels,
            last: Played::default(),
            totals: Totals::default(),
        }
    }

    /// Sample rate in frames per second.
    #[must_use]
    pub fn rate(&self) -> u32 {
        self.rate
    }

    /// Number of audio channels.
    #[must_use]
    pub fn channels_u8(&self) -> u8 {
        self.channels
    }

    /// The receiver of the core.
    #[must_use]
    pub fn receiver(&self) -> &Receiver<N, M, K> {
        &self.receiver
    }

    /// Enables [`unisono_core::sync::Sync`]-driven playback regulation with
    /// `regulation`.
    pub fn enable_sync(&mut self, regulation: ModalRegulation) {
        self.receiver.enable_sync(regulation);
    }

    /// Applies an O(1) clock synchronization snapshot published from the
    /// network thread, preserving any explicit fixed path delay override.
    pub fn apply_sync(&mut self, snapshot: SyncSnapshot) {
        self.receiver.apply_sync(snapshot);
        if let Some(path) = self.told_path {
            self.receiver.path(path);
        }
    }

    /// Tells the receiver the smallest delay of a packet from the sender, in
    /// nanoseconds. A receiver that is told it keeps it: the sender's
    /// answers to its reports are no longer taken in.
    pub fn path(&mut self, path: i64) {
        self.receiver.path(path);
        self.told_path = Some(path);
    }

    /// Makes the next report to send back to the sender, or `None` when no
    /// timeline is followed yet.
    pub fn report(&mut self) -> Option<Report> {
        self.receiver.report()
    }

    /// The largest needs of the last stretches of the followed timeline, for
    /// a report to carry.
    #[must_use]
    pub fn recent(&self) -> Recent {
        self.needs.recent()
    }

    /// Records the reading of the host's clock when report `sequence` left
    /// the host.
    pub fn reported(&mut self, sequence: u64, departure: i64) {
        self.receiver.reported(sequence, departure);
    }

    /// Takes in the sender's answer to a report, from which the delay of
    /// the path is measured, unless that delay was told.
    pub fn echo(&mut self, echo: &Echo) {
        if self.told_path.is_none() {
            self.receiver.echo(echo);
        }
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
        if heard.adopted || heard.restarted {
            self.needs.clear();
            self.timeline_played = false;
        }
        self.observe_need(header, &heard);
        if !heard.ignored {
            let receiver = &self.receiver;
            self.store
                .write_packet(header.index, header.format, payload, |index| {
                    receiver.covers(index)
                });
        }
        Some(heard)
    }

    /// Takes in the need of the first frame of a packet that the receiver
    /// took in: the latency at which it would just have been in time. A
    /// frame is in time if it is there when the playhead reaches it, so its
    /// need is the level less the time that the playhead takes to get to it.
    /// Only while frames are played on the current timeline does the playhead
    /// keep to the level.
    fn observe_need(&mut self, header: &Audio, heard: &Heard) {
        let marked = heard.marked;
        if heard.ignored
            || heard.adopted
            || heard.restarted
            || (marked.stored == 0 && marked.late == 0)
            || !self.timeline_played
            || self.last.played == 0
        {
            return;
        }
        let Some(stretch) = header.index.checked_div(u64::from(header.window)) else {
            return;
        };
        // Ignore packets from stretches behind the kept `RECENT` window so a
        // late duplicate cannot trigger `Needs::observe`'s far-jump clear.
        if let Some(newest) = self.needs.newest()
            && stretch.saturating_add(RECENT as u64) <= newest
        {
            return;
        }
        let ahead = i128::from(header.index) - i128::from(self.receiver.playhead());
        let Some(time) = (ahead * 1_000_000_000).checked_div(i128::from(header.rate)) else {
            return;
        };
        let need = i128::from(header.level) - time;
        self.needs.observe(
            stretch,
            i64::try_from(need).unwrap_or(if need < 0 { i64::MIN } else { i64::MAX }),
        );
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

    /// The revisions of the schedule so far.
    #[must_use]
    pub fn revisions(&self) -> Revisions {
        self.revisions
    }

    /// Takes in the revision of the schedule at the start of a cycle: `due`
    /// is the position that is due there, and `jumped` whether the cycle
    /// jumped to the schedule, which begins anew.
    fn revise(&mut self, due: Option<timing::Position>, jumped: bool) {
        let revision = match (self.expected, due) {
            (Some(expected), Some(due)) if !jumped => {
                // In units of 2^-32 frame; far below 2^53 of them.
                #[allow(clippy::cast_precision_loss)]
                let frames = timing::distance(expected, due) as f64 / 4_294_967_296.0;
                Some(frames)
            }
            _ => None,
        };
        if let Some(revision) = revision {
            self.revisions.add(revision, self.revised);
        }
        self.revised = revision;
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
        let due = self.receiver.due_at(start);
        let plan = self.receiver.cycle(start, duration, count);
        self.revise(due, plan.jumped);
        self.expected = self.receiver.due_at(start.saturating_add(duration));
        self.last = self
            .pump
            .play(&mut self.receiver, &self.store, &plan, frames);
        if self.last.played > 0 {
            self.timeline_played = true;
        }
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
            modal_regulation: None,
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

    #[test]
    fn settings_validation_rejects_invalid_receiver_parameters() {
        let valid = Settings {
            stream: 1,
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
        };
        assert!(valid.validate().is_ok());
        assert!(Settings { rate: 0, ..valid }.validate().is_err());
        assert!(
            Settings {
                channels: 0,
                ..valid
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                silence: -1,
                ..valid
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                slope_limit: 1_000_000_000,
                ..valid
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                regulation: Regulation {
                    jump: 0,
                    ..valid.regulation
                },
                ..valid
            }
            .validate()
            .is_err()
        );
        assert!(Settings { block: 0, ..valid }.validate().is_err());
    }

    #[test]
    fn resuming_during_fade_tail_without_jump_clears_synthetic_window_frames() {
        use unisono_core::packet::{Audio, Format};
        use unisono_core::player::Plan;
        use unisono_core::receiver::{self, Receiver};
        use unisono_dsp::{Filter, format::to_signed24};

        use super::{Pump, State};
        use crate::store::Store;

        let mut receiver = Receiver::<16, 16, 4>::new(receiver::Settings {
            stream: 1,
            identity: 1,
            silence: 1_000_000_000,
            limit: 200_000,
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
        });
        let mut store = Store::for_stretch(16, 1);
        let mut payload = vec![0u8; 512 * 3];
        to_signed24(&[0.5f32; 512], &mut payload);
        let header = Audio {
            stream: 1,
            timeline: 1,
            index: 0,
            capture: 0,
            rate: 48_000,
            frames: 512,
            channels: 1,
            format: Format::Signed24,
            level: 30_000_000,
            level_slope: 0,
            span: 2_000,
            window: 2_400,
            flags: 0,
            protection: 0,
            stamped_index: 0,
            stamped_departure: 0,
            drift: 0,
            clock: 1,
        };
        let _ = receiver.packet(&header, 1_000);
        store.write_packet(0, Format::Signed24, &payload, |i| receiver.covers(i));

        let mut pump = Pump::new(
            Filter::for_rate(48_000),
            1,
            Parameters::for_rate(48_000),
            128,
        );
        let mut out = vec![0.0f32; 64];
        let unity = Step::new(0).expect("unity step");
        // Active cycle playing frames 0..64.
        let plan1 = Plan {
            start: Position::new(0, 0),
            step: unity,
            frames: 64,
            jumped: true,
        };
        pump.play(&mut receiver, &store, &plan1, &mut out);
        assert!(matches!(pump.state, State::Playing { .. }));

        // Brief pause cycle (frames = 0) enters Fading and writes synthetic
        // fade-out frames into `pump.window`.
        let pause = Plan {
            start: Position::new(64, 0),
            step: unity,
            frames: 0,
            jumped: false,
        };
        pump.play(&mut receiver, &store, &pause, &mut out);
        assert!(matches!(pump.state, State::Fading { .. }));
        assert!(pump.length > 0);

        // Resume WITHOUT `jumped = true`: must keep real stream frames in the
        // window (no `behind` frames lost) while discarding synthetic fade-out
        // frames and fetching all 64 newly due real frames (`held == 64`).
        let resume = Plan {
            start: Position::new(64, 0),
            step: unity,
            frames: 64,
            jumped: false,
        };
        let played = pump.play(&mut receiver, &store, &resume, &mut out);
        assert_eq!(
            played.behind, 0,
            "resuming after fade-out must not discard real frames still in window: {played:?}"
        );
        assert_eq!(
            played.held, 64,
            "expected all 64 newly due real frames from store, got {played:?}"
        );
        let peak = out.iter().copied().fold(0.0f32, f32::max);
        assert!(
            peak > 0.1,
            "expected resumed fade-in output above 0.1 (was 0.037 when real frames were lost), peak={peak}, played={played:?}"
        );
        assert!(matches!(pump.state, State::Playing { .. }));
    }

    #[test]
    fn observe_need_skips_adoption_and_ignores_stale_stretches_without_wiping_needs() {
        use unisono_core::packet::{Audio, FLAG_STAMPED, Format};
        use unisono_dsp::format::to_signed24;

        use crate::audio::Playback;

        let mut playback = test_playback(48_000);
        playback.path(0);
        let mut payload = vec![0u8; 240 * 2 * 3];
        to_signed24(&[0.0f32; 480], &mut payload);
        let make_header = |timeline: u64, index: u64| {
            let capture = i64::try_from(index * 1_000_000_000 / 48_000).unwrap_or(0);
            let prev_index = index.saturating_sub(240);
            let prev_capture = i64::try_from(prev_index * 1_000_000_000 / 48_000).unwrap_or(0);
            Audio {
                stream: 1,
                timeline,
                index,
                capture,
                rate: 48_000,
                frames: 240,
                channels: 2,
                format: Format::Signed24,
                level: 30_000_000,
                level_slope: 0,
                span: 2_000,
                window: 240,
                flags: if index > 0 { FLAG_STAMPED } else { 0 },
                protection: 0,
                stamped_index: prev_index,
                stamped_departure: prev_capture,
                drift: 0,
                clock: 1,
            }
        };

        // Start timeline 1, play cycles so `last.played > 0`, and populate needs
        // up through stretch 30.
        for i in 0..32u64 {
            let h = make_header(1, i * 240);
            let arrival = h.capture + 1_000_000;
            playback.packet(&h, &payload, arrival);
            let mut out = [0.0f32; 480];
            playback.cycle(&mut out, i * 240, h.capture + 30_000_000);
        }
        let newest_before = playback.needs.newest().expect("needs recorded");
        assert!(newest_before >= 25, "newest {newest_before}");

        // A very late packet from stretch 0 (far behind `newest - RECENT`)
        // must NOT wipe `needs`.
        let stale = make_header(1, 0);
        playback.packet(&stale, &payload, stale.capture + 200_000_000);
        assert_eq!(playback.needs.newest(), Some(newest_before));

        // Adopting a brand-new timeline 2 (even while `last.played > 0` from
        // timeline 1) must clear needs and NOT record a bogus need on adoption.
        let p0 = make_header(2, 0);
        let p1 = make_header(2, 240);
        playback.packet(&p0, &payload, 2_000_000_000);
        playback.packet(&p1, &payload, 2_005_000_000);
        assert_eq!(playback.needs.newest(), None);
    }
}
