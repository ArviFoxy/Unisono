// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Receivers that exchange messages only with the sender.
//!
//! Each receiver must play every frame a fixed latency after its capture, as
//! the sender's clock measures it. It learns the difference between the
//! sender's clock and its own from exchanges with the sender over links with
//! jitter and holds, and it hears nothing from the other receivers. This
//! module simulates the clocks, the exchanges and two ways of playing, so
//! that they can be compared on what the receivers play:
//!
//! * the baseline of `docs/fixed-playout-delay.pdf`, which steers towards the
//!   estimate from the latest exchange and corrects by at most its slew;
//! * the best estimate with the law of `docs/star-optimum.pdf`: of each group
//!   of exchanges, the one with the shortest round trip; a Kalman filter for
//!   the offset and the relative frequency of the two clocks; and the law of
//!   `Unisono.Model.Regulation` applied to the estimate.
//!
//! A receiver's playback is described by the offset it plays at: the
//! difference between the sender's clock and its own that its positions
//! assume. Its error is that offset minus the true difference, in seconds:
//! the error of its latency, as the sender's clock measures it.
//!
//! The module also simulates the second-order model of the specification
//! with several receivers, to measure how a broadcast of the common part
//! changes synchronization, and the late arrivals of a stream through a link
//! with holds.

use crate::TrueTime;
use crate::link::{Link, LinkModel};
use crate::random::Generator;

/// The noise of an oscillator's fractional frequency.
#[derive(Clone, Copy, Debug)]
pub struct FrequencyNoise {
    /// The level of white frequency noise: the one-sided spectral density of
    /// the fractional frequency, in 1/Hz. The phase gains a variance of half
    /// this level per second.
    pub white: f64,
    /// The variance that the random walk adds to the fractional frequency per
    /// second.
    pub walk: f64,
}

/// The number of whole steps of `step` seconds in `duration` seconds,
/// rounded up.
fn step_count(duration: f64, step: f64) -> usize {
    // The ratio is positive and far below 2^52 in every simulation here.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let count = (duration / step).ceil() as usize;
    count
}

/// A count as a float, for averages.
fn as_float(count: usize) -> f64 {
    // Counts here stay far below 2^52.
    #[allow(clippy::cast_precision_loss)]
    let value = count as f64;
    value
}

/// The course of an oscillator's phase, its reading minus true time, in
/// seconds, drawn at a fixed step.
#[derive(Clone, Debug)]
pub struct PhaseCourse {
    step: f64,
    phases: Vec<f64>,
}

impl PhaseCourse {
    /// Draws the course over `duration` seconds from the phase `offset` and
    /// the fractional frequency `frequency`, with the noise `noise`.
    #[must_use]
    pub fn draw(
        offset: f64,
        frequency: f64,
        noise: FrequencyNoise,
        step: f64,
        duration: f64,
        generator: &mut Generator,
    ) -> PhaseCourse {
        let count = step_count(duration, step) + 2;
        let mut phases = Vec::with_capacity(count);
        let mut phase = offset;
        let mut fractional = frequency;
        for _ in 0..count {
            phases.push(phase);
            phase += fractional * step + (noise.white / 2.0 * step).sqrt() * generator.normal();
            fractional += (noise.walk * step).sqrt() * generator.normal();
        }
        PhaseCourse { step, phases }
    }

    /// The phase at true time `t` seconds, interpolated between the steps.
    #[must_use]
    pub fn at(&self, t: f64) -> f64 {
        let position = (t / self.step).max(0.0);
        // The position is not negative and within the drawn course.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let index = (position.floor() as usize).min(self.phases.len() - 2);
        let fraction = position - as_float(index);
        self.phases[index] + fraction * (self.phases[index + 1] - self.phases[index])
    }

    /// The clock's reading at true time `t`.
    #[must_use]
    pub fn reading(&self, t: f64) -> f64 {
        t + self.at(t)
    }
}

/// One exchange of a receiver with the sender, as the receiver sees it.
#[derive(Clone, Copy, Debug)]
pub struct Exchange {
    /// The estimate `t₂ - (t₁ + t₄) / 2` of the sender's clock minus the
    /// receiver's clock.
    pub offset: f64,
    /// The round trip `t₄ - t₁`, on the receiver's clock.
    pub round_trip: f64,
    /// The receiver's reading in the middle of the exchange, `(t₁ + t₄) / 2`.
    pub middle: f64,
    /// The true time at which the answer arrives.
    pub arrival: f64,
}

/// The exchanges of a receiver that sends a clock query every `period`
/// seconds of true time from `start` on, over the links `forward` (to the
/// sender) and `backward` (from the sender).
#[must_use]
pub fn exchanges(
    sender: &PhaseCourse,
    receiver: &PhaseCourse,
    forward: &mut Link,
    backward: &mut Link,
    period: f64,
    start: f64,
    duration: f64,
) -> Vec<Exchange> {
    let mut result = Vec::new();
    let mut sent = start;
    while sent < duration {
        let arrived = forward.arrival(TrueTime::from_seconds(sent)).seconds();
        let answered = backward.arrival(TrueTime::from_seconds(arrived)).seconds();
        let t1 = receiver.reading(sent);
        let t2 = sender.reading(arrived);
        let t4 = receiver.reading(answered);
        result.push(Exchange {
            offset: t2 - f64::midpoint(t1, t4),
            round_trip: t4 - t1,
            middle: f64::midpoint(t1, t4),
            arrival: answered,
        });
        sent += period;
    }
    result
}

/// The baseline's offset at each cycle of `cycle` seconds: it steers towards
/// the estimate of the latest exchange that has arrived, correcting by at
/// most `slew` seconds per second, and starts at the first estimate.
#[must_use]
pub fn baseline(exchanges: &[Exchange], cycle: f64, cycles: usize, slew: f64) -> Vec<Option<f64>> {
    let mut offsets = Vec::with_capacity(cycles);
    let mut next = 0;
    let mut target: Option<f64> = None;
    let mut played: Option<f64> = None;
    for k in 0..cycles {
        let now = as_float(k) * cycle;
        while next < exchanges.len() && exchanges[next].arrival <= now {
            target = Some(exchanges[next].offset);
            next += 1;
        }
        played = match (played, target) {
            (Some(previous), Some(goal)) => {
                let limit = slew * cycle;
                Some(previous + (goal - previous).clamp(-limit, limit))
            }
            (None, Some(goal)) => Some(goal),
            (previous, None) => previous,
        };
        offsets.push(played);
    }
    offsets
}

/// A Kalman filter for the offset and the relative frequency of two clocks.
#[derive(Clone, Debug)]
pub struct OffsetFilter {
    /// The estimate of the offset, in seconds.
    pub offset: f64,
    /// The estimate of the relative fractional frequency.
    pub frequency: f64,
    covariance: [[f64; 2]; 2],
    noise: FrequencyNoise,
}

impl OffsetFilter {
    /// A filter that starts at `offset` with the variance `offset_variance`,
    /// and at frequency zero with the variance `frequency_variance`, for the
    /// combined noise `noise` of the two clocks.
    #[must_use]
    pub fn new(
        offset: f64,
        offset_variance: f64,
        frequency_variance: f64,
        noise: FrequencyNoise,
    ) -> OffsetFilter {
        OffsetFilter {
            offset,
            frequency: 0.0,
            covariance: [[offset_variance, 0.0], [0.0, frequency_variance]],
            noise,
        }
    }

    /// Moves the estimate `dt` seconds ahead.
    pub fn predict(&mut self, dt: f64) {
        self.offset += self.frequency * dt;
        let [[a, b], [_, d]] = self.covariance;
        let white = self.noise.white / 2.0;
        let walk = self.noise.walk;
        let next_a = a + 2.0 * b * dt + d * dt * dt + white * dt + walk * dt * dt * dt / 3.0;
        let next_b = b + d * dt + walk * dt * dt / 2.0;
        let next_d = d + walk * dt;
        self.covariance = [[next_a, next_b], [next_b, next_d]];
    }

    /// Takes in a measurement `measured` of the offset `lag` seconds ago, with
    /// error variance `variance`.
    pub fn update(&mut self, measured: f64, lag: f64, variance: f64) {
        let [[a, b], [_, d]] = self.covariance;
        // The measurement is h · state with h = (1, -lag).
        let ha = a - lag * b;
        let hb = b - lag * d;
        let innovation_variance = ha - lag * hb + variance + self.noise.white / 2.0 * lag.abs();
        let gain_offset = ha / innovation_variance;
        let gain_frequency = hb / innovation_variance;
        let innovation = measured - (self.offset - lag * self.frequency);
        self.offset += gain_offset * innovation;
        self.frequency += gain_frequency * innovation;
        self.covariance = [
            [a - gain_offset * ha, b - gain_offset * hb],
            [b - gain_offset * hb, d - gain_frequency * hb],
        ];
    }

    /// The variance of the offset's estimate.
    #[must_use]
    pub fn offset_variance(&self) -> f64 {
        self.covariance[0][0]
    }
}

/// The law of `Unisono.Model.Regulation` with gain `g`: the change of the
/// pace for the distance `distance` behind the estimate and the pace `pace`
/// beyond the expected advance.
#[must_use]
pub fn law(g: f64, distance: f64, pace: f64) -> f64 {
    g * g / (2.0 - g) * distance - g * pace
}

/// How the best estimate with the law plays.
#[derive(Clone, Copy, Debug)]
pub struct EstimateSetting {
    /// The number of consecutive exchanges of which the one with the shortest
    /// round trip is measured.
    pub group: usize,
    /// The variance of that measurement's error, in square seconds.
    pub measurement_variance: f64,
    /// The combined frequency noise of the sender's and the receiver's clocks.
    pub noise: FrequencyNoise,
    /// The law's gain.
    pub gain: f64,
}

/// The offset of the best estimate with the law at each cycle of `cycle`
/// seconds. Each group of exchanges gives one measurement, its exchange with
/// the shortest round trip, once all of its exchanges have arrived.
#[must_use]
pub fn estimate_with_law(
    exchanges: &[Exchange],
    receiver: &PhaseCourse,
    cycle: f64,
    cycles: usize,
    setting: EstimateSetting,
) -> Vec<Option<f64>> {
    let groups: Vec<(f64, Exchange)> = exchanges
        .chunks(setting.group)
        .filter(|chunk| chunk.len() == setting.group)
        .map(|chunk| {
            let ready = chunk.iter().map(|e| e.arrival).fold(f64::MIN, f64::max);
            let best = chunk
                .iter()
                .copied()
                .min_by(|x, y| x.round_trip.total_cmp(&y.round_trip))
                .unwrap_or(chunk[0]);
            (ready, best)
        })
        .collect();
    let mut offsets = Vec::with_capacity(cycles);
    let mut next = 0;
    let mut filter: Option<OffsetFilter> = None;
    // The offset played and the number of seconds the last cycle advanced it.
    let mut played: Option<(f64, f64)> = None;
    for k in 0..cycles {
        let now = as_float(k) * cycle;
        if let Some(f) = filter.as_mut() {
            f.predict(cycle);
        }
        while next < groups.len() && groups[next].0 <= now {
            let (_, measured) = groups[next];
            let lag = receiver.reading(now) - measured.middle;
            match filter.as_mut() {
                Some(f) => f.update(measured.offset, lag, setting.measurement_variance),
                None => {
                    filter = Some(OffsetFilter::new(
                        measured.offset,
                        setting.measurement_variance,
                        1e-10,
                        setting.noise,
                    ));
                }
            }
            next += 1;
        }
        played = match (played, filter.as_ref()) {
            (Some((offset, read)), Some(f)) => {
                let distance = f.offset - offset;
                let pace = read - f.frequency * cycle;
                let next_read = read + law(setting.gain, distance, pace);
                Some((offset + next_read, next_read))
            }
            (None, Some(f)) => Some((f.offset, f.frequency * cycle)),
            (previous, None) => previous,
        };
        offsets.push(played.map(|(offset, _)| offset));
    }
    offsets
}

/// What a way of playing achieves over a run, from the end of the warm-up on.
#[derive(Clone, Copy, Debug, Default)]
pub struct Outcome {
    /// The root mean square, over the cycles, of the standard deviation of
    /// the receivers' errors at each cycle, in seconds.
    pub spread: f64,
    /// The root mean square of the receivers' errors, in seconds.
    pub error: f64,
    /// The root mean square of the change of the playback speed from one
    /// cycle to the next.
    pub speed_change: f64,
    /// The largest change of the playback speed from one cycle to the next.
    pub largest_speed_change: f64,
}

/// What the receivers' offsets `played` achieve against the true offsets
/// `truth`, over the cycles from `first` on.
#[must_use]
pub fn outcome(
    played: &[Vec<Option<f64>>],
    truth: &[Vec<f64>],
    cycle: f64,
    first: usize,
) -> Outcome {
    let receivers = played.len();
    let cycles = played.iter().map(Vec::len).min().unwrap_or(0);
    let mut spread_sum = 0.0;
    let mut error_sum = 0.0;
    let mut speed_sum = 0.0;
    let mut largest: f64 = 0.0;
    let mut counted = 0;
    let mut speed_counted = 0;
    for k in first.max(2)..cycles {
        let errors: Vec<f64> = (0..receivers)
            .filter_map(|r| played[r][k].map(|p| p - truth[r][k]))
            .collect();
        if errors.len() != receivers {
            continue;
        }
        let mean = errors.iter().sum::<f64>() / as_float(receivers);
        spread_sum += errors.iter().map(|e| (e - mean).powi(2)).sum::<f64>() / as_float(receivers);
        error_sum += errors.iter().map(|e| e * e).sum::<f64>() / as_float(receivers);
        counted += 1;
        for row in played {
            if let (Some(a), Some(b), Some(c)) = (row[k - 2], row[k - 1], row[k]) {
                let change = (c - 2.0 * b + a) / cycle;
                speed_sum += change * change;
                largest = largest.max(change.abs());
                speed_counted += 1;
            }
        }
    }
    if counted == 0 {
        return Outcome::default();
    }
    Outcome {
        spread: (spread_sum / as_float(counted)).sqrt(),
        error: (error_sum / as_float(counted)).sqrt(),
        speed_change: (speed_sum / as_float(speed_counted.max(1))).sqrt(),
        largest_speed_change: largest,
    }
}

/// A receiver of a comparison: its link in both directions, its clock, and
/// the variance of the error of its measurement.
#[derive(Clone, Copy, Debug)]
pub struct ReceiverSetting {
    /// The link to the sender and the link from it.
    pub link: LinkModel,
    /// The noise of the receiver's clock.
    pub clock: FrequencyNoise,
    /// The variance of the error of the exchange with the shortest round trip
    /// in a group, in square seconds, which the Kalman filter assumes.
    pub measurement_variance: f64,
}

/// A comparison of the baseline with the best estimate and the law.
#[derive(Clone, Debug)]
pub struct Comparison {
    /// Seconds per cycle.
    pub cycle: f64,
    /// Seconds between two clock queries of a receiver.
    pub period: f64,
    /// Exchanges per group of the best estimate's measurement.
    pub group: usize,
    /// Seconds simulated.
    pub duration: f64,
    /// Seconds before the outcome is counted.
    pub warmup: f64,
    /// The baseline's slew, in seconds per second.
    pub slew: f64,
    /// The law's gain.
    pub gain: f64,
    /// The noise of the sender's clock.
    pub sender: FrequencyNoise,
    /// The receivers.
    pub receivers: Vec<ReceiverSetting>,
}

/// The outcomes of the baseline and of the best estimate with the law, in
/// that order, for one run drawn from `seed`.
#[must_use]
pub fn compare(setting: &Comparison, seed: u64) -> (Outcome, Outcome) {
    let generator = Generator::new(seed);
    let step = 1e-3;
    let length = setting.duration + 5.0;
    let sender = PhaseCourse::draw(
        0.0,
        0.0,
        setting.sender,
        step,
        length,
        &mut generator.fork(1),
    );
    let cycles = step_count(setting.duration, setting.cycle);
    let first = step_count(setting.warmup, setting.cycle);
    let mut base = Vec::new();
    let mut best = Vec::new();
    let mut truth = Vec::new();
    for (index, receiver) in setting.receivers.iter().enumerate() {
        let label = 10 + 10 * u64::try_from(index).unwrap_or(0);
        let mut draws = generator.fork(label);
        let frequency = 2e-5 * (draws.uniform() - 0.5);
        let offset = draws.uniform() - 0.5;
        let clock = PhaseCourse::draw(offset, frequency, receiver.clock, step, length, &mut draws);
        let mut forward = Link::new(receiver.link, generator.fork(label + 1));
        let mut backward = Link::new(receiver.link, generator.fork(label + 2));
        let start = setting.period * draws.uniform();
        let measured = exchanges(
            &sender,
            &clock,
            &mut forward,
            &mut backward,
            setting.period,
            start,
            setting.duration,
        );
        base.push(baseline(&measured, setting.cycle, cycles, setting.slew));
        let noise = FrequencyNoise {
            white: setting.sender.white + receiver.clock.white,
            walk: setting.sender.walk + receiver.clock.walk,
        };
        best.push(estimate_with_law(
            &measured,
            &clock,
            setting.cycle,
            cycles,
            EstimateSetting {
                group: setting.group,
                measurement_variance: receiver.measurement_variance,
                noise,
                gain: setting.gain,
            },
        ));
        truth.push(
            (0..cycles)
                .map(|k| {
                    let t = as_float(k) * setting.cycle;
                    sender.at(t) - clock.at(t)
                })
                .collect::<Vec<f64>>(),
        );
    }
    (
        outcome(&base, &truth, setting.cycle, first),
        outcome(&best, &truth, setting.cycle, first),
    )
}

/// The spread of the errors over groups of receivers, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct Spreads {
    /// The root mean square of the standard deviation over all receivers.
    pub all: f64,
    /// The root mean square of the difference between two receivers of the
    /// first kind.
    pub first_kind: f64,
    /// The root mean square of the difference between a receiver of the
    /// first kind and one of the second.
    pub mixed: f64,
}

/// Two receivers' kinds in the second-order model: how many receivers of
/// each kind, and the standard deviation of each kind's measurement error.
#[derive(Clone, Copy, Debug)]
pub struct Kinds {
    /// Receivers of the first kind.
    pub first: usize,
    /// Receivers of the second kind.
    pub second: usize,
    /// The standard deviation of a measurement of the first kind, in seconds.
    pub first_error: f64,
    /// The standard deviation of a measurement of the second kind, in seconds.
    pub second_error: f64,
}

/// Sums of squared differences of errors, for `Spreads`.
#[derive(Clone, Copy, Debug, Default)]
struct SpreadSums {
    all: f64,
    first_kind: f64,
    mixed: f64,
    steps: usize,
    first_pairs: usize,
    mixed_pairs: usize,
}

impl SpreadSums {
    /// Adds the errors of one step; the first `first` receivers are of the
    /// first kind.
    fn add(&mut self, errors: &[f64], first: usize) {
        let mean = errors.iter().sum::<f64>() / as_float(errors.len());
        self.all += errors.iter().map(|e| (e - mean).powi(2)).sum::<f64>() / as_float(errors.len());
        self.steps += 1;
        for r in 0..errors.len() {
            for s in r + 1..errors.len() {
                let square = (errors[r] - errors[s]).powi(2);
                if s < first {
                    self.first_kind += square;
                    self.first_pairs += 1;
                } else if r < first {
                    self.mixed += square;
                    self.mixed_pairs += 1;
                }
            }
        }
    }

    fn finish(&self) -> Spreads {
        let root = |sum: f64, count: usize| {
            if count == 0 {
                0.0
            } else {
                (sum / as_float(count)).sqrt()
            }
        };
        Spreads {
            all: root(self.all, self.steps),
            first_kind: root(self.first_kind, self.first_pairs),
            mixed: root(self.mixed, self.mixed_pairs),
        }
    }
}

/// A phase and a fractional frequency that follow the noise `noise`, moved
/// `interval` seconds ahead.
fn advance(
    state: &mut (f64, f64),
    noise: FrequencyNoise,
    interval: f64,
    generator: &mut Generator,
) {
    state.0 += state.1 * interval + (noise.white / 2.0 * interval).sqrt() * generator.normal();
    state.1 += (noise.walk * interval).sqrt() * generator.normal();
}

/// Synchronization in the second-order model with several receivers, without
/// and with a broadcast of the common part, in that order.
///
/// The sender's clock and every receiver's clock follow their noise. Every
/// `interval` seconds each receiver measures the difference of the sender's
/// clock and its own, with white error of its kind. Without the broadcast,
/// each receiver estimates that difference with its own Kalman filter. With
/// it, the sender averages the measurements with weights inversely
/// proportional to their variances and broadcasts the average. Every receiver
/// estimates the broadcast with the same filter, which follows the part
/// common to all, and its measurement minus the broadcast with a filter of
/// its own.
#[must_use]
pub fn broadcast_comparison(
    kinds: Kinds,
    sender: FrequencyNoise,
    receiver: FrequencyNoise,
    interval: f64,
    steps: usize,
    seed: u64,
) -> (Spreads, Spreads) {
    let count = kinds.first + kinds.second;
    let mut generator = Generator::new(seed);
    let error_of = |r: usize| {
        if r < kinds.first {
            kinds.first_error
        } else {
            kinds.second_error
        }
    };
    let weights: Vec<f64> = (0..count).map(|r| 1.0 / error_of(r).powi(2)).collect();
    let total: f64 = weights.iter().sum();
    let broadcast_variance = 1.0 / total;
    let both = FrequencyNoise {
        white: sender.white + receiver.white,
        walk: sender.walk + receiver.walk,
    };
    let mut own: Vec<OffsetFilter> = (0..count)
        .map(|r| OffsetFilter::new(0.0, error_of(r).powi(2), 1e-12, both))
        .collect();
    let mut residual: Vec<OffsetFilter> = (0..count)
        .map(|r| OffsetFilter::new(0.0, error_of(r).powi(2), 1e-12, receiver))
        .collect();
    let mut common = OffsetFilter::new(0.0, broadcast_variance, 1e-12, sender);
    let mut sender_phase = (0.0, 0.0);
    let mut phases = vec![(0.0, 0.0); count];
    let mut without = SpreadSums::default();
    let mut with = SpreadSums::default();
    for step in 0..steps {
        advance(&mut sender_phase, sender, interval, &mut generator);
        for phase in &mut phases {
            advance(phase, receiver, interval, &mut generator);
        }
        let truth: Vec<f64> = phases.iter().map(|p| sender_phase.0 - p.0).collect();
        let measured: Vec<f64> = (0..count)
            .map(|r| truth[r] + error_of(r) * generator.normal())
            .collect();
        let average = measured
            .iter()
            .zip(&weights)
            .map(|(m, w)| m * w)
            .sum::<f64>()
            / total;
        common.predict(interval);
        common.update(average, 0.0, broadcast_variance);
        let mut own_errors = Vec::with_capacity(count);
        let mut split_errors = Vec::with_capacity(count);
        for r in 0..count {
            own[r].predict(interval);
            own[r].update(measured[r], 0.0, error_of(r).powi(2));
            own_errors.push(own[r].offset - truth[r]);
            residual[r].predict(interval);
            residual[r].update(
                measured[r] - average,
                0.0,
                error_of(r).powi(2) + broadcast_variance,
            );
            split_errors.push(common.offset + residual[r].offset - truth[r]);
        }
        if step >= steps / 10 {
            without.add(&own_errors, kinds.first);
            with.add(&split_errors, kinds.first);
        }
    }
    (without.finish(), with.finish())
}

/// The fraction of the packets of a stream, one sent every `cycle` seconds
/// for `duration` seconds through a link that follows `link`, that arrive
/// more than `margin` seconds after they are sent.
#[must_use]
pub fn late_fraction(link: LinkModel, cycle: f64, duration: f64, margin: f64, seed: u64) -> f64 {
    let mut path = Link::new(link, Generator::new(seed));
    let packets = step_count(duration, cycle);
    let late = (0..packets)
        .filter(|&k| {
            let sent = as_float(k) * cycle;
            path.arrival(TrueTime::from_seconds(sent)).seconds() - sent > margin
        })
        .count();
    as_float(late) / as_float(packets.max(1))
}

/// The margin that the quantile rule chooses for holds that start at `rate`
/// per second with exponentially distributed lengths of mean `mean`, when a
/// second of latency costs `price_ratio` times as much as a second of missed
/// playback: the margin beyond which holds are rarer than `price_ratio` per
/// second.
#[must_use]
pub fn hold_margin(rate: f64, mean: f64, price_ratio: f64) -> f64 {
    if rate <= price_ratio {
        0.0
    } else {
        mean * (rate / price_ratio).ln()
    }
}

/// The fraction of time that holds starting at `rate` per second, with
/// exponentially distributed lengths of mean `mean`, keep beyond the margin
/// `margin`, by Campbell's formula: `rate * mean * exp(-margin / mean)`.
#[must_use]
pub fn campbell_fraction(rate: f64, mean: f64, margin: f64) -> f64 {
    rate * mean * (-margin / mean).exp()
}
