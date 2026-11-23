// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! One-way network link impairment and shared contention models.
//!
//! Implements the per-link delay decomposition of
//! `Unisono.Spec.Models.Delays` (drifting minimum baseline, exponential-tail
//! queueing jitter, hold-and-release pauses, packet-dropping burst outages,
//! independent drops, and reordering) together with the time-indexed shared
//! host TX/RX and wireless access-point contention of
//! `Unisono.Spec.Models.SecondOrder`.

use crate::random::Generator;
use crate::{TrueTime, seconds_to_nanos};

/// Parameters of a directed network link. All durations are in seconds.
#[derive(Clone, Copy, Debug)]
pub struct LinkModel {
    /// Minimum one-way propagation delay at `t = 0`, in seconds.
    pub minimum: f64,
    /// Linear drift rate of the minimum baseline delay (`d(baseline)/dt`), in
    /// seconds per second.
    pub baseline_slope: f64,
    /// Mean excess delay of a packet that meets no queue, in seconds.
    pub clear_excess: f64,
    /// Probability that a packet meets a queue, in `[0, 1]`.
    pub queued: f64,
    /// Mean excess delay of a packet that meets a queue, in seconds.
    pub queued_excess: f64,
    /// Mean arrival rate of hold-and-release pauses, in pauses per second.
    pub pause_rate: f64,
    /// Mean duration of a hold-and-release pause, in seconds.
    pub pause_length: f64,
    /// Mean arrival rate of packet-dropping burst outages, in outages per
    /// second.
    pub outage_rate: f64,
    /// Mean duration of a packet-dropping burst outage, in seconds.
    pub outage_length: f64,
    /// Independent per-packet random drop probability, in `[0, 1)`.
    pub drop_rate: f64,
    /// Probability that a packet is held up on its own so later packets can
    /// overtake it, in `[0, 1]`.
    pub overtaken: f64,
    /// Mean extra delay of an overtaken packet, in seconds.
    pub overtaken_excess: f64,
    /// Whether non-overtaken packets preserve FIFO arrival order.
    pub preserve_order: bool,
    /// Standard deviation of transmit-side timestamping error, in seconds.
    pub tx_timestamp_std: f64,
    /// Standard deviation of receive-side timestamping error, in seconds.
    pub rx_timestamp_std: f64,
}

impl LinkModel {
    /// Noiseless FIFO link with 100 us minimum delay and zero jitter, loss,
    /// pauses, outages, or timestamp error.
    pub const IDEAL: LinkModel = LinkModel {
        minimum: 100e-6,
        baseline_slope: 0.0,
        clear_excess: 0.0,
        queued: 0.0,
        queued_excess: 0.0,
        pause_rate: 0.0,
        pause_length: 0.0,
        outage_rate: 0.0,
        outage_length: 0.0,
        drop_rate: 0.0,
        overtaken: 0.0,
        overtaken_excess: 0.0,
        preserve_order: true,
        tx_timestamp_std: 0.0,
        rx_timestamp_std: 0.0,
    };

    /// Switched wired Ethernet link under light background traffic.
    pub const WIRED_CALM: LinkModel = LinkModel {
        minimum: 100e-6,
        baseline_slope: 0.0,
        clear_excess: 5e-6,
        queued: 0.1,
        queued_excess: 200e-6,
        pause_rate: 0.0,
        pause_length: 0.0,
        outage_rate: 0.0,
        outage_length: 0.0,
        drop_rate: 0.0,
        overtaken: 0.0,
        overtaken_excess: 0.0,
        preserve_order: true,
        tx_timestamp_std: 2e-6,
        rx_timestamp_std: 2e-6,
    };

    /// Switched wired Ethernet link under heavy queueing load with occasional
    /// short stalls.
    pub const WIRED_BUSY: LinkModel = LinkModel {
        minimum: 100e-6,
        baseline_slope: 0.0,
        clear_excess: 20e-6,
        queued: 0.6,
        queued_excess: 500e-6,
        pause_rate: 1.0 / 60.0,
        pause_length: 30e-3,
        outage_rate: 0.0,
        outage_length: 0.0,
        drop_rate: 0.0,
        overtaken: 0.0,
        overtaken_excess: 0.0,
        preserve_order: true,
        tx_timestamp_std: 10e-6,
        rx_timestamp_std: 10e-6,
    };

    /// Wireless LAN link with contention jitter, occasional pauses, and mild
    /// random loss.
    pub const WIRELESS: LinkModel = LinkModel {
        minimum: 1e-3,
        baseline_slope: 0.0,
        clear_excess: 300e-6,
        queued: 0.5,
        queued_excess: 3e-3,
        pause_rate: 1.0 / 20.0,
        pause_length: 30e-3,
        outage_rate: 0.0,
        outage_length: 0.0,
        drop_rate: 0.02,
        overtaken: 0.0,
        overtaken_excess: 0.0,
        preserve_order: true,
        tx_timestamp_std: 10e-6,
        rx_timestamp_std: 10e-6,
    };

    /// Bursty wireless link with pauses, packet-dropping burst outages, random
    /// loss, and occasional packet reordering.
    pub const WIRELESS_BURSTY: LinkModel = LinkModel {
        minimum: 1e-3,
        baseline_slope: 0.0,
        clear_excess: 300e-6,
        queued: 0.5,
        queued_excess: 3e-3,
        pause_rate: 1.0 / 20.0,
        pause_length: 50e-3,
        outage_rate: 0.1,
        outage_length: 20e-3,
        drop_rate: 0.02,
        overtaken: 0.01,
        overtaken_excess: 5e-3,
        preserve_order: true,
        tx_timestamp_std: 15e-6,
        rx_timestamp_std: 15e-6,
    };
}

/// Lazy sorted, non-overlapping schedule of Poisson-arriving episodes with
/// exponentially distributed lengths (used for both hold-and-release pauses and
/// packet-dropping burst outages).
#[derive(Clone, Debug)]
struct EpisodeSchedule {
    rate: f64,
    mean_length: f64,
    /// Merged non-overlapping `[start, end)` intervals in seconds, sorted by
    /// `start`.
    episodes: Vec<(f64, f64)>,
    /// True time (seconds) up to which all episodes have been generated.
    horizon: f64,
    /// Last drawn Poisson arrival time.
    cursor: f64,
    /// Pending episode start already drawn beyond `horizon`.
    next_start: Option<f64>,
    generator: Generator,
}

impl EpisodeSchedule {
    fn new(rate: f64, mean_length: f64, generator: Generator) -> Self {
        Self {
            rate,
            mean_length,
            episodes: Vec::new(),
            horizon: 0.0,
            cursor: 0.0,
            next_start: None,
            generator,
        }
    }

    fn extend_to(&mut self, until: f64) {
        if !(until.is_finite()
            && self.rate.is_finite()
            && self.rate > 0.0
            && self.mean_length.is_finite()
            && self.mean_length > 0.0)
        {
            if until.is_finite() {
                self.horizon = self.horizon.max(until);
            }
            return;
        }
        if until <= self.horizon {
            return;
        }
        let mean_gap = 1.0 / self.rate;
        if !(mean_gap.is_finite() && mean_gap > 0.0) {
            self.horizon = self.horizon.max(until);
            return;
        }
        loop {
            let start = if let Some(pending) = self.next_start {
                pending
            } else {
                let step = self.generator.exponential(mean_gap);
                let next = self.cursor + step;
                if !(next.is_finite() && next > self.cursor) {
                    break;
                }
                self.cursor = next;
                next
            };
            if start > until {
                self.next_start = Some(start);
                break;
            }
            self.next_start = None;
            let length = self.generator.exponential(self.mean_length);
            let end = start + length;
            if !end.is_finite() {
                break;
            }
            match self.episodes.last_mut() {
                Some(last) if last.1 >= start => last.1 = last.1.max(end),
                _ => self.episodes.push((start, end)),
            }
        }
        self.horizon = self.horizon.max(until);
    }

    fn active_end(&self, t_s: f64) -> Option<f64> {
        let idx = self.episodes.partition_point(|ep| ep.0 <= t_s);
        idx.checked_sub(1)
            .and_then(|pos| self.episodes.get(pos))
            .filter(|ep| t_s < ep.1)
            .map(|ep| ep.1)
    }

    fn is_active(&mut self, t_s: f64) -> bool {
        if !t_s.is_finite() {
            return false;
        }
        self.extend_to(t_s);
        self.active_end(t_s).is_some()
    }

    /// Returns the first true time `u >= t_s` at which no episode is active
    /// (matching `Unisono.Spec.Link.release`).
    fn release_time(&mut self, t_s: f64) -> f64 {
        if !t_s.is_finite() {
            return t_s;
        }
        let mut released = t_s;
        for _ in 0..1_024 {
            self.extend_to(released);
            if let Some(end) = self.active_end(released)
                && end > released
            {
                released = end;
            } else {
                break;
            }
        }
        released
    }
}

/// A simulated directed network link from one host to another.
///
/// Packets are sent at non-decreasing true times. Hold-and-release pauses delay
/// release until the pause ends; burst outages active at release time and
/// independent per-packet drops discard the packet; non-overtaken packets keep
/// FIFO arrival order when `preserve_order` is enabled.
#[derive(Clone, Debug)]
pub struct Link {
    model: LinkModel,
    generator: Generator,
    stamp_rng: Generator,
    pauses: EpisodeSchedule,
    outages: EpisodeSchedule,
    last_arrival: TrueTime,
}

impl Link {
    /// Creates a link that follows `model`, drawing its stochastic impairments
    /// from independent forks of `generator`.
    #[must_use]
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(model: LinkModel, generator: Generator) -> Link {
        let pauses = EpisodeSchedule::new(model.pause_rate, model.pause_length, generator.fork(1));
        let outages =
            EpisodeSchedule::new(model.outage_rate, model.outage_length, generator.fork(2));
        Link {
            model,
            generator: generator.fork(3),
            stamp_rng: generator.fork(4),
            pauses,
            outages,
            last_arrival: TrueTime::ZERO,
        }
    }

    /// Returns the immutable parameters of this link.
    #[must_use]
    pub fn model(&self) -> LinkModel {
        self.model
    }

    fn finish_delivery(&mut self, sent_s: f64, release_s: f64, shared_jitter_s: f64) -> TrueTime {
        let floor = if self.model.minimum > 0.0 { 1e-9 } else { 0.0 };
        let baseline_s = (self.model.minimum + self.model.baseline_slope * release_s).max(floor);
        let excess_s = if self.model.queued > 0.0 && self.generator.chance(self.model.queued) {
            if self.model.queued_excess > 0.0 {
                self.generator.exponential(self.model.queued_excess)
            } else {
                0.0
            }
        } else if self.model.clear_excess > 0.0 {
            self.generator.exponential(self.model.clear_excess)
        } else {
            0.0
        };
        let shared_s = if shared_jitter_s.is_finite() {
            shared_jitter_s.max(0.0)
        } else {
            0.0
        };
        let unhindered = TrueTime::from_seconds(sent_s + baseline_s + excess_s + shared_s);
        let paused_release = TrueTime::from_seconds(release_s + baseline_s + shared_s);
        let base_arrival = unhindered.max(paused_release);
        let arrival = if self.model.preserve_order {
            base_arrival.max(self.last_arrival)
        } else {
            base_arrival
        };
        if self.model.overtaken > 0.0 && self.generator.chance(self.model.overtaken) {
            let held = if self.model.overtaken_excess > 0.0 {
                self.generator.exponential(self.model.overtaken_excess)
            } else {
                0.0
            };
            return arrival.plus_seconds(held);
        }
        if self.model.preserve_order {
            self.last_arrival = arrival;
        }
        arrival
    }

    /// Delivers a packet sent at true time `sent` with optional external shared
    /// contention delay `shared_jitter_s` (seconds).
    ///
    /// Returns `None` if the link is in a burst outage at the packet's release
    /// time or if the packet suffers an independent random drop.
    pub fn deliver(&mut self, sent: TrueTime, shared_jitter_s: f64) -> Option<TrueTime> {
        let sent_s = sent.seconds();
        let release_s = self.pauses.release_time(sent_s);
        if self.outages.is_active(release_s) {
            return None;
        }
        if self.model.drop_rate > 0.0 && self.generator.chance(self.model.drop_rate) {
            return None;
        }
        Some(self.finish_delivery(sent_s, release_s, shared_jitter_s))
    }

    /// Non-dropping arrival time of a packet sent at `sent` (backward-compatible
    /// helper for callers that model packet loss separately).
    pub fn arrival(&mut self, sent: TrueTime) -> TrueTime {
        let sent_s = sent.seconds();
        let release_s = self.pauses.release_time(sent_s);
        self.finish_delivery(sent_s, release_s, 0.0)
    }

    /// Perturbs a true transmit clock reading (in nanoseconds) by zero-mean
    /// Gaussian transmit timestamp noise with standard deviation
    /// `tx_timestamp_std`.
    pub fn stamp_tx(&mut self, true_reading_ns: i64) -> i64 {
        if self.model.tx_timestamp_std > 0.0 && self.model.tx_timestamp_std.is_finite() {
            let error_s = self.model.tx_timestamp_std * self.stamp_rng.normal();
            true_reading_ns.saturating_add(seconds_to_nanos(error_s))
        } else {
            true_reading_ns
        }
    }

    /// Perturbs a true receive clock reading (in nanoseconds) by zero-mean
    /// Gaussian receive timestamp noise with standard deviation
    /// `rx_timestamp_std`.
    pub fn stamp_rx(&mut self, true_reading_ns: i64) -> i64 {
        if self.model.rx_timestamp_std > 0.0 && self.model.rx_timestamp_std.is_finite() {
            let error_s = self.model.rx_timestamp_std * self.stamp_rng.normal();
            true_reading_ns.saturating_add(seconds_to_nanos(error_s))
        } else {
            true_reading_ns
        }
    }
}

/// Configuration for time-indexed shared host TX/RX and wireless access-point
/// contention delays, matching the `tx(i, u) + rx(j, u)` jitter decomposition
/// of `Unisono.Spec.Models.SecondOrder`.
#[derive(Clone, Debug)]
pub struct SharedContentionModel {
    /// Mean shared outgoing (TX) stack contention delay per host, in seconds.
    pub tx_means: Vec<f64>,
    /// Mean shared incoming (RX) stack contention delay per host, in seconds.
    pub rx_means: Vec<f64>,
    /// Mean shared wireless access-point contention delay, in seconds.
    pub ap_mean: f64,
    /// Whether each host uses the shared wireless medium (`true` adds the
    /// shared AP contention delay to links leaving or arriving at that host).
    pub wireless_hosts: Vec<bool>,
    /// Discrete time-slot width of the shared contention grid, in seconds.
    pub slot_s: f64,
    /// Exponential autocorrelation time constant across slots, in seconds
    /// (`0.0` produces independent slots).
    pub correlation_s: f64,
}

impl SharedContentionModel {
    /// Creates a zero-contention model for `hosts` hosts.
    #[must_use]
    pub fn none(hosts: usize) -> SharedContentionModel {
        SharedContentionModel {
            tx_means: vec![0.0; hosts],
            rx_means: vec![0.0; hosts],
            ap_mean: 0.0,
            wireless_hosts: vec![false; hosts],
            slot_s: 1e-3,
            correlation_s: 0.0,
        }
    }

    /// Creates a contention model with uniform per-host outgoing/incoming stack
    /// delay means and a shared wireless AP delay for hosts marked in
    /// `wireless_hosts`.
    #[must_use]
    pub fn uniform(
        hosts: usize,
        outgoing_mean: f64,
        incoming_mean: f64,
        ap_mean: f64,
        wireless_hosts: Vec<bool>,
    ) -> SharedContentionModel {
        SharedContentionModel {
            tx_means: vec![outgoing_mean; hosts],
            rx_means: vec![incoming_mean; hosts],
            ap_mean,
            wireless_hosts,
            slot_s: 1e-3,
            correlation_s: 5e-3,
        }
    }
}

/// Lazy time-indexed stationary exponential AR(1) (Lawrence-Lewis EAR(1))
/// delay process on slots of width `slot_s` seconds.
///
/// Every slot has an exact `Exp(mean)` marginal (nonnegative, exponential tail,
/// coming arbitrarily close to zero) and exact lag autocorrelation
/// `exp(-m * slot_s / correlation_s)`.
#[derive(Clone, Debug)]
struct ContentionChannel {
    mean: f64,
    rho: f64,
    slot_s: f64,
    values: Vec<f64>,
    generator: Generator,
}

impl ContentionChannel {
    fn new(mean: f64, slot_s: f64, correlation_s: f64, generator: Generator) -> Self {
        let valid_mean = if mean.is_finite() && mean > 0.0 {
            mean
        } else {
            0.0
        };
        let valid_slot = if slot_s.is_finite() && slot_s > 0.0 {
            slot_s
        } else {
            1e-3
        };
        let rho = if correlation_s.is_finite() && correlation_s > 0.0 {
            (-valid_slot / correlation_s).exp().clamp(0.0, 0.999_999)
        } else {
            0.0
        };
        Self {
            mean: valid_mean,
            rho,
            slot_s: valid_slot,
            values: Vec::new(),
            generator,
        }
    }

    fn at(&mut self, at: TrueTime) -> f64 {
        if self.mean <= 0.0 {
            return 0.0;
        }
        let t_s = at.seconds().max(0.0);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let slot = (t_s / self.slot_s).floor() as usize;
        if self.values.is_empty() {
            let first = self.generator.exponential(self.mean);
            self.values.push(first);
        }
        while self.values.len() <= slot {
            let prev = self.values.last().copied().unwrap_or(0.0);
            let innovation = if self.rho > 0.0 && self.generator.chance(self.rho) {
                0.0
            } else {
                self.generator.exponential(self.mean)
            };
            self.values.push(self.rho * prev + innovation);
        }
        self.values[slot]
    }
}

/// Time-indexed generator for shared per-host TX/RX stack contention and shared
/// wireless access-point contention delays.
#[derive(Clone, Debug)]
pub struct SharedContention {
    outgoing_channels: Vec<ContentionChannel>,
    incoming_channels: Vec<ContentionChannel>,
    ap_channel: ContentionChannel,
    wireless_hosts: Vec<bool>,
}

impl SharedContention {
    /// Creates a shared contention generator from `model` and `generator`.
    #[must_use]
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(model: SharedContentionModel, generator: Generator) -> SharedContention {
        let outgoing_channels = model
            .tx_means
            .into_iter()
            .enumerate()
            .map(|(idx, mean)| {
                ContentionChannel::new(
                    mean,
                    model.slot_s,
                    model.correlation_s,
                    generator.fork(1_000 + u64::try_from(idx).unwrap_or(0)),
                )
            })
            .collect();
        let incoming_channels = model
            .rx_means
            .into_iter()
            .enumerate()
            .map(|(idx, mean)| {
                ContentionChannel::new(
                    mean,
                    model.slot_s,
                    model.correlation_s,
                    generator.fork(2_000 + u64::try_from(idx).unwrap_or(0)),
                )
            })
            .collect();
        let ap_channel = ContentionChannel::new(
            model.ap_mean,
            model.slot_s,
            model.correlation_s,
            generator.fork(3_000),
        );
        SharedContention {
            outgoing_channels,
            incoming_channels,
            ap_channel,
            wireless_hosts: model.wireless_hosts,
        }
    }

    /// Returns host `host`'s shared outgoing (TX) contention delay at `at`, in
    /// seconds.
    pub fn tx_delay(&mut self, host: usize, at: TrueTime) -> f64 {
        self.outgoing_channels
            .get_mut(host)
            .map_or(0.0, |chan| chan.at(at))
    }

    /// Returns host `host`'s shared incoming (RX) contention delay at `at`, in
    /// seconds.
    pub fn rx_delay(&mut self, host: usize, at: TrueTime) -> f64 {
        self.incoming_channels
            .get_mut(host)
            .map_or(0.0, |chan| chan.at(at))
    }

    /// Returns the shared wireless access-point contention delay at `at`, in
    /// seconds.
    pub fn ap_delay(&mut self, at: TrueTime) -> f64 {
        self.ap_channel.at(at)
    }

    /// Returns the total shared contention delay (`tx(src, at) + rx(dst, at)`
    /// plus `ap(at)` if either endpoint is wireless) in seconds.
    pub fn delay(&mut self, src: usize, dst: usize, at: TrueTime) -> f64 {
        let outgoing = self.tx_delay(src, at);
        let incoming = self.rx_delay(dst, at);
        let on_wireless = self.wireless_hosts.get(src).copied().unwrap_or(false)
            || self.wireless_hosts.get(dst).copied().unwrap_or(false);
        let shared_ap = if on_wireless { self.ap_delay(at) } else { 0.0 };
        outgoing + incoming + shared_ap
    }
}

#[cfg(test)]
mod tests {
    use super::{Link, LinkModel, SharedContention, SharedContentionModel};
    use crate::TrueTime;
    use crate::random::Generator;

    const MODEL: LinkModel = LinkModel {
        minimum: 100e-6,
        clear_excess: 5e-6,
        queued: 0.1,
        queued_excess: 200e-6,
        ..LinkModel::IDEAL
    };

    #[test]
    fn no_packet_is_faster_than_the_smallest_delay_and_order_is_kept() {
        let mut link = Link::new(MODEL, Generator::new(5));
        let mut previous = TrueTime::ZERO;
        for k in 0..10_000 {
            let sent = TrueTime(k * 1_000_000);
            let arrival = link.arrival(sent);
            assert!(arrival.0 - sent.0 >= 100_000, "delay below the minimum");
            assert!(arrival >= previous, "arrivals out of order");
            previous = arrival;
        }
    }

    /// The mean excess is `0.9 * 5 us + 0.1 * 200 us = 24.5 us`; over 100,000
    /// packets sent far enough apart not to queue behind each other, the
    /// sample mean is within 1 us of that.
    #[test]
    fn the_mean_excess_is_the_mixture_of_the_two_kinds() {
        let mut link = Link::new(MODEL, Generator::new(6));
        let n = 100_000;
        let total: i64 = (0..n)
            .map(|k| link.arrival(TrueTime(k * 10_000_000)).0 - k * 10_000_000 - 100_000)
            .sum();
        #[allow(clippy::cast_precision_loss)]
        let mean = total as f64 / n as f64 * 1e-9;
        assert!((mean - 24.5e-6).abs() < 1e-6, "mean excess {mean}");
    }

    #[test]
    fn a_packet_held_up_on_its_own_is_overtaken() {
        let model = LinkModel {
            overtaken: 0.05,
            overtaken_excess: 10e-3,
            ..MODEL
        };
        let mut link = Link::new(model, Generator::new(8));
        let arrivals: Vec<i64> = (0..10_000)
            .map(|k| link.arrival(TrueTime(k * 1_000_000)).0)
            .collect();
        let overtaken = arrivals.windows(2).filter(|pair| pair[1] < pair[0]).count();
        assert!((300..700).contains(&overtaken), "overtaken {overtaken}");
        for (k, arrival) in (0i64..).zip(&arrivals) {
            assert!(
                arrival - k * 1_000_000 >= 100_000,
                "delay below the minimum"
            );
        }
    }

    #[test]
    fn a_pause_holds_packets_back_and_releases_them_together() {
        let model = LinkModel {
            pause_rate: 1.0,
            pause_length: 0.05,
            ..MODEL
        };
        let mut link = Link::new(model, Generator::new(7));
        let arrivals: Vec<(i64, i64)> = (0..20_000)
            .map(|k| (k * 1_000_000, link.arrival(TrueTime(k * 1_000_000)).0))
            .collect();
        let longest = arrivals
            .iter()
            .map(|(sent, arrival)| arrival - sent)
            .max()
            .unwrap_or(0);
        assert!(
            longest > 20_000_000,
            "no pause was felt: longest delay {longest} ns"
        );
        let compressed = arrivals
            .windows(2)
            .filter(|pair| pair[1].1 - pair[0].1 < 100_000)
            .count();
        assert!(
            compressed > 100,
            "held packets were not released together: {compressed}"
        );
    }

    #[test]
    fn drops_and_burst_outages_discard_packets_at_expected_rates() {
        let random_drop = LinkModel {
            drop_rate: 0.15,
            ..LinkModel::IDEAL
        };
        let mut link = Link::new(random_drop, Generator::new(11));
        let total = 20_000_i64;
        let dropped = (0..total)
            .filter(|&k| link.deliver(TrueTime(k * 1_000_000), 0.0).is_none())
            .count();
        #[allow(clippy::cast_precision_loss)]
        let rate = dropped as f64 / total as f64;
        assert!((0.13..0.17).contains(&rate), "drop rate {rate}");

        // Burst outages: 1 outage/s of mean 50 ms (~4.8% outage fraction) in
        // contiguous runs rather than isolated packets.
        let burst = LinkModel {
            outage_rate: 1.0,
            outage_length: 0.05,
            ..LinkModel::IDEAL
        };
        let mut burst_link = Link::new(burst, Generator::new(12));
        let mut longest_run = 0_usize;
        let mut curr_run = 0_usize;
        let mut total_lost = 0_usize;
        for k in 0..40_000_i64 {
            if burst_link.deliver(TrueTime(k * 1_000_000), 0.0).is_none() {
                curr_run += 1;
                total_lost += 1;
                longest_run = longest_run.max(curr_run);
            } else {
                curr_run = 0;
            }
        }
        assert!(total_lost > 800, "too few outage drops: {total_lost}");
        assert!(
            longest_run > 20,
            "outage drops were not bursty: longest_run={longest_run}"
        );

        // Non-finite / zero rates are handled defensively without looping.
        let degenerate = LinkModel {
            pause_rate: f64::INFINITY,
            pause_length: 0.05,
            outage_rate: f64::NAN,
            outage_length: 0.05,
            ..LinkModel::IDEAL
        };
        let mut deg_link = Link::new(degenerate, Generator::new(13));
        assert!(deg_link.deliver(TrueTime::from_seconds(1.0), 0.0).is_some());
    }

    #[test]
    fn preserve_order_toggles_fifo_vs_natural_reordering() {
        let base = LinkModel {
            minimum: 100e-6,
            clear_excess: 5e-3,
            queued: 0.0,
            queued_excess: 0.0,
            ..LinkModel::IDEAL
        };
        let mut fifo = Link::new(base, Generator::new(19));
        let mut unordered = Link::new(
            LinkModel {
                preserve_order: false,
                ..base
            },
            Generator::new(19),
        );
        let mut fifo_reorders = 0_usize;
        let mut free_reorders = 0_usize;
        let mut prev_fifo = TrueTime::ZERO;
        let mut prev_free = TrueTime::ZERO;
        for k in 0..5_000_i64 {
            let sent = TrueTime(k * 1_000_000);
            let arr_fifo = fifo.deliver(sent, 0.0).expect("no loss");
            let arr_free = unordered.deliver(sent, 0.0).expect("no loss");
            if arr_fifo < prev_fifo {
                fifo_reorders += 1;
            }
            if arr_free < prev_free {
                free_reorders += 1;
            }
            prev_fifo = arr_fifo;
            prev_free = arr_free;
        }
        assert_eq!(fifo_reorders, 0);
        assert!(
            free_reorders > 500,
            "expected reordering without preserve_order, got {free_reorders}"
        );
    }

    #[test]
    fn baseline_slope_shifts_minimum_delay_linearly() {
        let drifting = LinkModel {
            minimum: 1e-3,
            baseline_slope: 2e-5, // +20 us per second
            ..LinkModel::IDEAL
        };
        let mut link = Link::new(drifting, Generator::new(21));
        let early = link.deliver(TrueTime::ZERO, 0.0).expect("no loss");
        let late = link
            .deliver(TrueTime::from_seconds(50.0), 0.0)
            .expect("no loss");
        // At t = 0: 1.0 ms; at t = 50 s: 1.0 ms + 50 * 20 us = 2.0 ms.
        assert_eq!(early.0, 1_000_000);
        assert_eq!(late.0 - 50_000_000_000, 2_000_000);
    }

    #[test]
    fn shared_contention_correlates_links_sharing_host_or_wireless_ap() {
        let model = SharedContentionModel {
            tx_means: vec![500e-6, 0.0, 0.0, 0.0],
            rx_means: vec![0.0; 4],
            ap_mean: 800e-6,
            wireless_hosts: vec![false, true, true, false],
            slot_s: 1e-3,
            correlation_s: 5e-3,
        };
        let mut contention = SharedContention::new(model, Generator::new(31));
        let mut first_link = Link::new(LinkModel::WIRED_CALM, Generator::new(32));
        let mut second_link = Link::new(LinkModel::WIRED_CALM, Generator::new(33));

        let n = 5_000_i64;
        let mut xs = Vec::with_capacity(5_000);
        let mut ys = Vec::with_capacity(5_000);
        let mut ap_prev = Vec::with_capacity(5_000);
        let mut ap_next = Vec::with_capacity(5_000);
        for k in 0..n {
            let sent = TrueTime(k * 10_000_000);
            let shared_one = contention.delay(0, 1, sent);
            let shared_two = contention.delay(0, 2, sent);
            // Both share host 0 TX and wireless AP contention at `sent`.
            assert!((shared_one - shared_two).abs() < 1e-15);
            let arr_one = first_link.deliver(sent, shared_one).expect("no loss");
            let arr_two = second_link.deliver(sent, shared_two).expect("no loss");
            #[allow(clippy::cast_precision_loss)]
            {
                xs.push((arr_one.0 - sent.0) as f64 * 1e-9);
                ys.push((arr_two.0 - sent.0) as f64 * 1e-9);
            }
            ap_prev.push(contention.ap_delay(sent));
            ap_next.push(contention.ap_delay(sent.plus_seconds(1e-3)));
        }
        let corr = |a: &[f64], b: &[f64]| -> f64 {
            #[allow(clippy::cast_precision_loss)]
            let len = a.len() as f64;
            let ma = a.iter().sum::<f64>() / len;
            let mb = b.iter().sum::<f64>() / len;
            let cov: f64 = a.iter().zip(b).map(|(u, v)| (u - ma) * (v - mb)).sum();
            let va: f64 = a.iter().map(|u| (u - ma).powi(2)).sum();
            let vb: f64 = b.iter().map(|v| (v - mb).powi(2)).sum();
            cov / (va * vb).sqrt()
        };
        let cross_corr = corr(&xs, &ys);
        assert!(
            cross_corr > 0.9,
            "links sharing TX + AP contention must be strongly correlated, got {cross_corr}"
        );
        // Lag-1 ms autocorrelation of EAR(1) with tau = 5 ms is exp(-0.2) ~ 0.819.
        let lag1_corr = corr(&ap_prev, &ap_next);
        let expected_lag1 = (-0.2_f64).exp();
        assert!(
            (lag1_corr - expected_lag1).abs() < 0.06,
            "EAR(1) lag-1 autocorrelation {lag1_corr} vs {expected_lag1}"
        );
    }

    #[test]
    fn timestamp_noise_matches_configured_tx_and_rx_standard_deviations() {
        let model = LinkModel {
            tx_timestamp_std: 4e-6,
            rx_timestamp_std: 12e-6,
            ..LinkModel::IDEAL
        };
        let mut link = Link::new(model, Generator::new(41));
        let samples = 20_000_i32;
        let base_ns = 1_000_000_000_i64;
        let mut send_sq = 0.0;
        let mut recv_sq = 0.0;
        for _ in 0..samples {
            #[allow(clippy::cast_precision_loss)]
            let send_err = (link.stamp_tx(base_ns) - base_ns) as f64 * 1e-9;
            #[allow(clippy::cast_precision_loss)]
            let recv_err = (link.stamp_rx(base_ns) - base_ns) as f64 * 1e-9;
            send_sq += send_err * send_err;
            recv_sq += recv_err * recv_err;
        }
        let send_std = (send_sq / f64::from(samples)).sqrt();
        let recv_std = (recv_sq / f64::from(samples)).sqrt();
        assert!(
            (send_std - 4e-6).abs() < 0.25e-6,
            "tx std {send_std} vs 4e-6"
        );
        assert!(
            (recv_std - 12e-6).abs() < 0.75e-6,
            "rx std {recv_std} vs 12e-6"
        );
    }
}
