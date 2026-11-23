// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Discrete-event multi-receiver stream simulator driving `unisono_core`.
//!
//! Models a sender host (host clock + capture oscillator) and one or more
//! receiver hosts (each with a host clock, link from sender, and per-speaker
//! playback oscillators). Records per-cycle timing error: true sender clock
//! time when the cycle's first frame leaves the DAC minus `(capture + level)`
//! (positive means playing late).

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use unisono_core::device::Device;
use unisono_core::packet::{Audio, Echo, Format, Report};
use unisono_core::player::Regulation;
use unisono_core::receiver::{Receiver, Settings as ReceiverSettings};
use unisono_core::sender::{Sender, Settings};
use unisono_core::timing::advance;

use crate::clock::{Course, OscillatorModel};
use crate::link::{Link, LinkModel};
use crate::random::Generator;
use crate::{TrueTime, seconds_to_nanos};

/// A receiver with room for 4,096 frames, 64 samples of the sender's clock
/// and the arrivals of 8 packets.
pub type SimReceiver = Receiver<64, 64, 8>;

/// How many frames before and after a position the resampler reads.
const FILTER_REACH: u64 = 24;

/// Maximum relative deviation from nominal rate accepted from a fitted device
/// line (1%, matching `ReceiverPlayback`'s default `device_range`).
const DEVICE_RANGE: u32 = 10_000_000;

/// What the sender is like.
#[derive(Clone, Copy, Debug)]
pub struct SenderModel {
    /// The oscillator of its clock.
    pub clock: OscillatorModel,
    /// The oscillator of its capture device.
    pub device: OscillatorModel,
    /// Frames per second.
    pub rate: u32,
    /// Frames in a packet.
    pub packet_frames: u16,
    /// The latency that every receiver holds, in nanoseconds.
    pub level: i64,
    /// Seconds from the capture of a packet's last frame to its departure.
    pub send_delay: f64,
    /// How long receivers remember samples of the sender's clock, in
    /// milliseconds.
    pub span: u32,
    /// Frames in a window of that estimate.
    pub window: u32,
}

/// What a host of receivers is like.
#[derive(Clone, Copy, Debug)]
pub struct HostModel {
    /// The oscillator of its clock.
    pub clock: OscillatorModel,
    /// The link from the sender to it.
    pub link: LinkModel,
    /// The link from it back to the sender.
    pub back: LinkModel,
}

/// How a receiver learns how long a cycle of its device takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CycleLength {
    /// From its device: the time between the first frames of two cycles on
    /// its own clock.
    Measured,
    /// From the nominal rate alone, as if the device ran exactly at it. This
    /// is a mistake that a receiver could make.
    Nominal,
    /// From the line fitted to the reports of its audio system, which give
    /// the time of each cycle's first frame with an error of up to this
    /// many nanoseconds either way.
    Fitted(i64),
}

/// How a receiver learns the smallest delay of the link from the sender.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathDelay {
    /// It is told the true value.
    Told,
    /// It sends reports, this many nanoseconds apart, and takes half the
    /// smallest delay there and back from the sender's answers.
    Measured(i64),
    /// It takes the delay to be zero.
    Unknown,
}

/// What a receiver is like.
#[derive(Clone, Copy, Debug)]
pub struct ReceiverModel {
    /// Which host it is on.
    pub host: usize,
    /// The oscillator of its playback device.
    pub device: OscillatorModel,
    /// Frames in a cycle of the device.
    pub cycle_frames: u32,
    /// Seconds from the planning of a cycle to the time its first frame
    /// leaves the device.
    pub lead: f64,
    /// The settings of its regulator.
    pub regulation: Regulation,
    /// After how many nanoseconds of silence it takes up another timeline
    /// or starts anew.
    pub silence: i64,
    /// The largest slope of its estimate of the sender's clock, in
    /// nanoseconds per second.
    pub slope_limit: i64,
    /// How it learns the smallest delay of its link.
    pub path: PathDelay,
    /// How it learns the length of a cycle.
    pub cycle_length: CycleLength,
    /// A cycle before which its device stands still, and for how many
    /// seconds: the frames from that cycle on leave the device that much
    /// later than the device's count of frames says.
    pub stands_still: Option<(u64, f64)>,
}

/// What a receiver did over a run.
#[derive(Clone, Debug, Default)]
pub struct Trace {
    /// For every cycle that played frames: the true time, in seconds, at
    /// which its first frame left the device, and the timing error, in
    /// seconds.
    pub errors: Vec<(f64, f64)>,
    /// The true times, in seconds, of the cycles whose position jumped.
    pub jumps: Vec<f64>,
    /// The number of cycles in which nothing was due.
    pub idle_cycles: u64,
    /// Frames given to the device that were held, and that were absent.
    pub held: u64,
    /// See `held`.
    pub absent: u64,
}

enum Event {
    /// The sender's next packet leaves, if the sender is still in `epoch`.
    Send { epoch: u64 },
    /// A packet arrives at a host.
    Arrive { host: usize, header: Audio },
    /// A receiver plans a cycle of its device.
    Plan { receiver: usize, cycle: u64 },
    /// A receiver sends a report.
    Report { receiver: usize },
    /// A report arrives at the sender.
    Answer { receiver: usize, report: Report },
    /// The sender's answer arrives at a receiver.
    Echo { receiver: usize, echo: Echo },
}

struct Host {
    clock: Course,
    link: Link,
    back: Link,
    path: i64,
}

struct Listener {
    model: ReceiverModel,
    core: SimReceiver,
    device: Course,
    /// The line fitted to the reports of the audio system.
    line: Device<64>,
    /// Fractional nanosecond carry (Q16) from fitted cycle durations, matching
    /// `ReceiverPlayback::step_device`.
    carried: i64,
    noise: Generator,
    trace: Trace,
}

impl Listener {
    /// When the frame that the device counts as `frame` leaves it.
    fn leaves(&mut self, frame: f64, rate: f64) -> TrueTime {
        let counted = self.device.when(frame / rate);
        match self.model.stands_still {
            // A count below 2^53 is exact as a float.
            #[allow(clippy::cast_precision_loss)]
            Some((cycle, seconds))
                if frame >= (cycle * u64::from(self.model.cycle_frames)) as f64 =>
            {
                counted.plus_seconds(seconds)
            }
            _ => counted,
        }
    }
}

/// A sender, hosts and receivers, and the events between them.
pub struct Scene {
    model: SenderModel,
    sender: Sender,
    clock: Course,
    capture: Course,
    /// The count of the capture device at which each timeline began.
    origins: Vec<(u64, f64)>,
    /// Counts the restarts of the sender, so that a packet planned before a
    /// restart is not sent after it.
    epoch: u64,
    hosts: Vec<Host>,
    listeners: Vec<Listener>,
    queue: BinaryHeap<Reverse<(TrueTime, usize)>>,
    events: Vec<Option<Event>>,
    now: TrueTime,
}

fn new_receiver(model: &ReceiverModel, identity: u64, path: i64) -> SimReceiver {
    let mut core = SimReceiver::new(ReceiverSettings {
        stream: 1,
        identity,
        silence: model.silence,
        limit: model.slope_limit,
        regulation: model.regulation,
    });
    if model.path == PathDelay::Told {
        core.path(path);
    }
    core
}

/// A position of a stream as a number of frames.
fn frames_of(position: unisono_core::timing::Position) -> f64 {
    // Exact to 2^-53 of the position, which is far below a nanosecond here.
    #[allow(clippy::cast_precision_loss)]
    let frames = position.frame as f64 + position.fraction as f64 / 18_446_744_073_709_551_616.0;
    frames
}

impl Scene {
    /// A scene with these parties, with all randomness drawn from
    /// `generator`.
    #[must_use]
    pub fn new(
        sender: SenderModel,
        hosts: &[HostModel],
        receivers: &[ReceiverModel],
        generator: &Generator,
    ) -> Scene {
        let settings = Settings {
            stream: 1,
            rate: sender.rate,
            channels: 2,
            format: Format::Signed24,
            span: sender.span,
            window: sender.window,
            clock: 1,
        };
        let hosts: Vec<Host> = hosts
            .iter()
            .zip(0u64..)
            .map(|(model, number)| Host {
                clock: Course::new(model.clock, generator.fork(100 + number)),
                link: Link::new(model.link, generator.fork(200 + number)),
                back: Link::new(model.back, generator.fork(400 + number)),
                path: seconds_to_nanos(model.link.minimum),
            })
            .collect();
        let listeners = receivers
            .iter()
            .zip(0u64..)
            .map(|(model, number)| Listener {
                model: *model,
                core: new_receiver(
                    model,
                    number,
                    hosts.get(model.host).map_or(0, |host| host.path),
                ),
                device: Course::new(model.device, generator.fork(300 + number)),
                line: Device::new(sender.rate),
                carried: 0,
                noise: generator.fork(500 + number),
                trace: Trace::default(),
            })
            .collect();
        let mut scene = Scene {
            model: sender,
            sender: Sender::new(settings, 1_000, sender.level),
            clock: Course::new(sender.clock, generator.fork(1)),
            capture: Course::new(sender.device, generator.fork(2)),
            origins: vec![(1_000, 0.0)],
            epoch: 0,
            hosts,
            listeners,
            queue: BinaryHeap::new(),
            events: Vec::new(),
            now: TrueTime::ZERO,
        };
        scene.plan_send();
        for receiver in 0..scene.listeners.len() {
            scene.plan_cycle(receiver, 1);
            scene.plan_report(receiver, TrueTime::ZERO);
        }
        scene
    }

    /// What each receiver did so far.
    #[must_use]
    pub fn traces(&self) -> Vec<&Trace> {
        self.listeners
            .iter()
            .map(|listener| &listener.trace)
            .collect()
    }

    /// A receiver's estimate of the smallest delay of its link, in
    /// nanoseconds.
    #[must_use]
    pub fn delay(&self, receiver: usize) -> Option<i64> {
        self.listeners
            .get(receiver)
            .map(|listener| listener.core.delay())
    }

    /// The timeline that a receiver follows, if any.
    #[must_use]
    pub fn followed(&self, receiver: usize) -> Option<u64> {
        self.listeners
            .get(receiver)
            .and_then(|listener| listener.core.timeline())
    }

    fn push(&mut self, at: TrueTime, event: Event) {
        self.queue.push(Reverse((at, self.events.len())));
        self.events.push(Some(event));
    }

    /// The count of the capture device at which the timeline began.
    fn origin(&self, timeline: u64) -> Option<f64> {
        self.origins
            .iter()
            .find(|(number, _)| *number == timeline)
            .map(|(_, origin)| *origin)
    }

    /// The true time at which the capture device captured the frame at
    /// `position` of `timeline`.
    fn captured(&mut self, timeline: u64, position: f64) -> Option<TrueTime> {
        let origin = self.origin(timeline)?;
        Some(
            self.capture
                .when((origin + position) / f64::from(self.model.rate)),
        )
    }

    /// Plans the departure of the sender's next packet.
    fn plan_send(&mut self) {
        // An index below 2^53 is exact as a float.
        #[allow(clippy::cast_precision_loss)]
        let last = self.sender.next() as f64 + f64::from(self.model.packet_frames);
        if let Some(captured) = self.captured(self.sender.timeline(), last) {
            let at = captured.plus_seconds(self.model.send_delay);
            self.push(at, Event::Send { epoch: self.epoch });
        }
    }

    /// Plans a cycle of a receiver's device.
    fn plan_cycle(&mut self, receiver: usize, cycle: u64) {
        let Some(listener) = self.listeners.get_mut(receiver) else {
            return;
        };
        // A count below 2^53 is exact as a float.
        #[allow(clippy::cast_precision_loss)]
        let first = (cycle * u64::from(listener.model.cycle_frames)) as f64;
        let leaves = listener.leaves(first, f64::from(self.model.rate));
        let at = leaves.plus_seconds(-listener.model.lead);
        self.push(at, Event::Plan { receiver, cycle });
    }

    /// Plans the next report of a receiver that measures its path, after
    /// true time `after`.
    fn plan_report(&mut self, receiver: usize, after: TrueTime) {
        let period = self
            .listeners
            .get(receiver)
            .map(|listener| listener.model.path);
        if let Some(PathDelay::Measured(period)) = period {
            self.push(
                TrueTime(after.0.saturating_add(period)),
                Event::Report { receiver },
            );
        }
    }

    /// Lets a receiver send a report at true time `at`.
    fn report(&mut self, receiver: usize, at: TrueTime) {
        let Some(listener) = self.listeners.get_mut(receiver) else {
            return;
        };
        let Some(host) = self.hosts.get_mut(listener.model.host) else {
            return;
        };
        if let Some(report) = listener.core.report() {
            listener.core.reported(report.sequence, host.clock.read(at));
            let arrival = host.back.arrival(at);
            self.push(arrival, Event::Answer { receiver, report });
        }
        self.plan_report(receiver, at);
    }

    /// Lets the sender answer a report that arrives at true time `at`.
    fn answer(&mut self, receiver: usize, report: &Report, at: TrueTime) {
        let reading = self.clock.read(at);
        let Some(echo) = self.sender.answer(report, reading, reading) else {
            return;
        };
        let host = self
            .listeners
            .get(receiver)
            .map(|listener| listener.model.host);
        let arrival = host
            .and_then(|host| self.hosts.get_mut(host))
            .map(|host| host.link.arrival(at));
        if let Some(arrival) = arrival {
            self.push(arrival, Event::Echo { receiver, echo });
        }
    }

    /// Lets the sender send its next packet at true time `at`.
    fn send(&mut self, at: TrueTime) {
        let timeline = self.sender.timeline();
        let index = self.sender.next();
        // An index below 2^53 is exact as a float.
        #[allow(clippy::cast_precision_loss)]
        let Some(captured) = self.captured(timeline, index as f64) else {
            return;
        };
        let pace =
            (1.0 + self.capture.frequency(captured)) / (1.0 + self.clock.frequency(captured));
        // A drift of clocks is far inside the range of 32 bits.
        #[allow(clippy::cast_possible_truncation)]
        let drift = ((pace - 1.0) * 1e9).round() as i32;
        let header = self
            .sender
            .packet(self.model.packet_frames, self.clock.read(captured), drift);
        // The stamp of this departure is known only afterwards, so the
        // packets after this one carry it.
        self.sender.departed(timeline, index, self.clock.read(at));
        for host in 0..self.hosts.len() {
            if let Some(arrival) = self.hosts.get_mut(host).map(|host| host.link.arrival(at)) {
                self.push(arrival, Event::Arrive { host, header });
            }
        }
        self.plan_send();
    }

    /// Lets a receiver plan and play a cycle of its device.
    fn cycle(&mut self, receiver: usize, cycle: u64) {
        let rate = f64::from(self.model.rate);
        let level = self.model.level;
        let Some(listener) = self.listeners.get_mut(receiver) else {
            return;
        };
        let Some(host) = self.hosts.get_mut(listener.model.host) else {
            return;
        };
        let frames = listener.model.cycle_frames;
        // A count below 2^53 is exact as a float.
        #[allow(clippy::cast_precision_loss)]
        let first = (cycle * u64::from(frames)) as f64;
        let leaves = listener.leaves(first, rate);
        let ends = listener.leaves(first + f64::from(frames), rate);
        let exact = host.clock.read(leaves);
        let (time, duration) = match listener.model.cycle_length {
            CycleLength::Measured => (exact, host.clock.read(ends) - exact),
            CycleLength::Nominal => (exact, seconds_to_nanos(f64::from(frames) / rate)),
            CycleLength::Fitted(error) => {
                // A count below 2^53 is exact as a float, and the error is
                // a small whole number.
                #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
                let off = ((listener.noise.uniform() * 2.0 - 1.0) * error as f64).round() as i64;
                let position = cycle * u64::from(frames);
                let observed = exact.saturating_add(off);
                listener.line.observe(position, observed);
                let nominal_q16 =
                    (i128::from(frames) << 16) * 1_000_000_000 / i128::from(self.model.rate.max(1));
                let (fitted_start, measured_q16) = listener
                    .line
                    .when_cycle(position, frames)
                    .map_or((observed, nominal_q16), |(s, d)| (s, i128::from(d)));
                let usable = listener.line.kept() > 1
                    && measured_q16 > 0
                    && (measured_q16 - nominal_q16).abs() * 1_000_000_000
                        <= nominal_q16 * i128::from(DEVICE_RANGE);
                let duration_q16 = if usable {
                    measured_q16
                } else {
                    listener.carried = 0;
                    nominal_q16
                };
                let exact_q16 = duration_q16 + i128::from(listener.carried);
                #[allow(clippy::cast_possible_truncation)] // masked to 16 bits
                {
                    listener.carried = (exact_q16 & 0xffff) as i64;
                }
                let duration = i64::try_from(exact_q16 >> 16).unwrap_or(i64::MAX);
                let start = if usable { fitted_start } else { observed };
                (start, duration)
            }
        };
        let plan = listener.core.cycle(time, duration, frames);
        if plan.frames == 0 {
            listener.trace.idle_cycles += 1;
        } else {
            if plan.jumped {
                listener.trace.jumps.push(leaves.seconds());
            }
            // What a shell does with a plan: it needs the frames around the
            // positions it reads, drops what a jump leaves behind, and takes
            // the rest in runs.
            let end = advance(plan.start, plan.frames, plan.step.offset());
            if plan.jumped {
                listener
                    .core
                    .skip(plan.start.frame.saturating_sub(FILTER_REACH));
            }
            let last = end.frame.saturating_add(FILTER_REACH);
            while listener.core.playhead() <= last {
                let wanted = last - listener.core.playhead() + 1;
                let segment = listener
                    .core
                    .take(u32::try_from(wanted).unwrap_or(u32::MAX));
                if segment.frames == 0 {
                    break;
                }
                if segment.held {
                    listener.trace.held += u64::from(segment.frames);
                } else {
                    listener.trace.absent += u64::from(segment.frames);
                }
            }
            let timeline = listener.core.timeline();
            let position = frames_of(plan.start);
            let played = self.clock.seconds(leaves);
            let captured = timeline.and_then(|timeline| self.captured(timeline, position));
            if let Some(captured) = captured {
                // A level in nanoseconds is exact as a float.
                #[allow(clippy::cast_precision_loss)]
                let due = self.clock.seconds(captured) + level as f64 * 1e-9;
                if let Some(listener) = self.listeners.get_mut(receiver) {
                    listener.trace.errors.push((leaves.seconds(), played - due));
                }
            }
        }
        self.plan_cycle(receiver, cycle + 1);
    }

    /// Runs the scene up to true time `until`.
    pub fn run(&mut self, until: TrueTime) {
        while let Some(Reverse((at, number))) = self.queue.peek().copied() {
            if at > until {
                break;
            }
            self.queue.pop();
            self.now = at;
            let Some(event) = self.events.get_mut(number).and_then(Option::take) else {
                continue;
            };
            match event {
                Event::Send { epoch } => {
                    if epoch == self.epoch {
                        self.send(at);
                    }
                }
                Event::Arrive { host, header } => {
                    let Some(stamp) = self.hosts.get_mut(host).map(|host| host.clock.read(at))
                    else {
                        continue;
                    };
                    for listener in &mut self.listeners {
                        if listener.model.host == host {
                            listener.core.packet(&header, stamp);
                        }
                    }
                }
                Event::Plan { receiver, cycle } => self.cycle(receiver, cycle),
                Event::Report { receiver } => self.report(receiver, at),
                Event::Answer { receiver, report } => self.answer(receiver, &report, at),
                Event::Echo { receiver, echo } => {
                    if let Some(listener) = self.listeners.get_mut(receiver) {
                        listener.core.echo(&echo);
                    }
                }
            }
        }
        self.now = until;
    }

    /// Restarts the sender now: it starts another timeline at the frame its
    /// device captures next.
    pub fn restart_sender(&mut self) {
        self.epoch += 1;
        self.sender.restart(0);
        let count = (f64::from(self.model.rate) * self.capture.seconds(self.now)).ceil();
        self.origins.push((self.sender.timeline(), count));
        self.plan_send();
    }

    /// Restarts a receiver now: it forgets everything but its settings.
    pub fn restart_receiver(&mut self, receiver: usize) {
        if let Some(listener) = self.listeners.get_mut(receiver) {
            let path = self
                .hosts
                .get(listener.model.host)
                .map_or(0, |host| host.path);
            listener.core = new_receiver(&listener.model, receiver as u64, path);
            listener.line = Device::new(self.model.rate);
            listener.carried = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::player::Regulation;

    use super::{CycleLength, HostModel, PathDelay, ReceiverModel, Scene, SenderModel};
    use crate::TrueTime;
    use crate::clock::OscillatorModel;
    use crate::link::LinkModel;
    use crate::random::Generator;

    #[test]
    fn restart_receiver_resets_fitted_device_line_and_carry() {
        let osc = OscillatorModel {
            offset: 0.0,
            frequency: 0.0,
            walk: 0.0,
        };
        let link = LinkModel {
            minimum: 1e-3,
            clear_excess: 0.0,
            queued: 0.0,
            queued_excess: 0.0,
            pause_rate: 0.0,
            pause_length: 0.0,
            overtaken: 0.0,
            overtaken_excess: 0.0,
        };
        let sender = SenderModel {
            clock: osc,
            device: osc,
            rate: 48_000,
            packet_frames: 240,
            level: 30_000_000,
            send_delay: 1e-4,
            span: 2_000,
            window: 2_400,
        };
        let hosts = [HostModel {
            clock: osc,
            link,
            back: link,
        }];
        let receivers = [ReceiverModel {
            host: 0,
            device: osc,
            cycle_frames: 256,
            lead: 4e-3,
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
            silence: 1_000_000_000,
            slope_limit: 200_000,
            path: PathDelay::Told,
            cycle_length: CycleLength::Fitted(50_000),
            stands_still: None,
        }];
        let mut scene = Scene::new(sender, &hosts, &receivers, &Generator::new(9));
        scene.run(TrueTime::from_seconds(0.5));
        assert!(scene.listeners[0].line.kept() > 10);

        scene.restart_receiver(0);
        assert_eq!(scene.listeners[0].line.kept(), 0);
        assert_eq!(scene.listeners[0].carried, 0);
    }
}
