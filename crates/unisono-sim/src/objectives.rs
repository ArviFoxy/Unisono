// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Exact Rust evaluation of the six canonical playback objectives in
//! `Unisono.Spec.Objectives` and the resampler lookahead constraint in
//! `Unisono.Spec.Solution.playable`.
//!
//! Provides:
//! * Primitive definitions (`is_continuous`, `is_playable`, `playable`,
//!   `missed_at`, `discontinuity_at`, `step_speed`, `roughness_between`,
//!   `play_time`, `captured_at`).
//! * Literal sample-array reference evaluator (`score_samples`).
//! * Compact streaming evaluator (`ObjectiveRecorder`) with exact first-cover
//!   `playTime` semantics, cross-break roughness, and bounded frame buffering.
//! * Order-statistic summary helper (`Quantiles`, `quantiles`).

use std::collections::VecDeque;

/// Converts a `usize` count or index to `f64`.
fn as_float(count: usize) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let value = count as f64;
    value
}

/// Converts a `u64` frame or event count to `f64`.
fn u64_to_f64(value: u64) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let float = value as f64;
    float
}

/// Whether playback is continuous from output sample `curr` to `next`,
/// matching `Unisono.Spec.PlaysContinuously`: both play the source and the
/// source position advances strictly between `0` and `2` frames.
#[must_use]
pub fn is_continuous(curr: Option<f64>, next: Option<f64>) -> bool {
    matches!(
        (curr, next),
        (Some(start_pos), Some(end_pos))
            if start_pos.is_finite()
                && end_pos.is_finite()
                && start_pos < end_pos
                && end_pos < start_pos + 2.0
    )
}

/// Whether source position `position` is playable with resampler lookahead
/// `lookahead` frames given held-frame predicate `is_held`, matching the
/// predicate of `Unisono.Spec.playable`:
/// `position >= 0` and every frame `n` with `|n - position| < lookahead` is
/// held.
#[must_use]
pub fn is_playable(position: f64, lookahead: usize, is_held: impl Fn(u64) -> bool) -> bool {
    if !position.is_finite() || position < 0.0 {
        return false;
    }
    if lookahead == 0 {
        return true;
    }
    let reach = as_float(lookahead);
    let lo = if position > reach {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        {
            (position - reach).floor().max(0.0) as u64
        }
    } else {
        0
    };
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let hi = (position + reach).ceil().max(0.0) as u64;
    for frame in lo..=hi {
        if (u64_to_f64(frame) - position).abs() < reach && !is_held(frame) {
            return false;
        }
    }
    true
}

/// Filters a chosen output sample position through the exact lookahead
/// playability constraint of `Unisono.Spec.playable`.
#[must_use]
pub fn playable(
    position: Option<f64>,
    lookahead: usize,
    is_held: impl Fn(u64) -> bool,
) -> Option<f64> {
    position.filter(|&pos| is_playable(pos, lookahead, is_held))
}

/// Internal O(1) evaluator of `Unisono.Spec.missedAt` given the most recent
/// prior output sample that played the source.
fn missed_at_step(curr: Option<f64>, k: usize, last_some: Option<(usize, f64)>) -> u64 {
    match curr {
        None => 1,
        Some(end_pos) => match last_some {
            Some((last_idx, start_pos))
                if last_idx < k && start_pos.is_finite() && end_pos.is_finite() =>
            {
                let advance = end_pos - start_pos;
                let gap = i64::try_from(k - 1 - last_idx).unwrap_or(i64::MAX);
                #[allow(clippy::cast_possible_truncation)]
                let skip_floor = (advance - 1.0).floor() as i64;
                let skipped = u64::try_from(skip_floor.saturating_sub(gap).max(0)).unwrap_or(0);
                #[allow(clippy::cast_possible_truncation)]
                let replay_floor = (1.0 - advance).floor() as i64;
                let replayed = u64::try_from(replay_floor.max(0)).unwrap_or(0);
                skipped.saturating_add(replayed)
            }
            _ => 0,
        },
    }
}

/// Missed samples counted at output sample `k` of `plays`, matching
/// `Unisono.Spec.missedAt`:
/// * `1` if `plays[k]` is `None`;
/// * otherwise, if an earlier output sample played the source, the count of
///   skipped frames beyond the intervening `None` gap plus the count of
///   replayed frames;
/// * `0` on the first sample that plays the source or out-of-bounds `k`.
#[must_use]
pub fn missed_at(plays: &[Option<f64>], k: usize) -> u64 {
    let Some(&curr) = plays.get(k) else {
        return 0;
    };
    let last_some = (0..k)
        .rev()
        .find_map(|idx| plays[idx].map(|pos| (idx, pos)));
    missed_at_step(curr, k, last_some)
}

/// Discontinuities counted at output sample `k` of `plays`, matching
/// `Unisono.Spec.discontinuityAt`: `1` if `plays[k]` plays the source and step
/// `k -> k + 1` is not continuous; `0` otherwise (including at the final
/// recorded sample where `k + 1` is outside the trace).
#[must_use]
pub fn discontinuity_at(plays: &[Option<f64>], k: usize) -> u64 {
    let Some(&curr) = plays.get(k) else {
        return 0;
    };
    let Some(&next) = plays.get(k + 1) else {
        return 0;
    };
    u64::from(curr.is_some() && !is_continuous(curr, next))
}

/// Linearly interpolated capture time of fractional source position `position`,
/// matching `Unisono.Spec.World.captured`.
#[must_use]
pub fn captured_at(capture_times: &[f64], position: f64) -> f64 {
    if capture_times.is_empty() || !position.is_finite() {
        return 0.0;
    }
    if capture_times.len() == 1 {
        return capture_times[0];
    }
    if position <= 0.0 {
        let step = capture_times[1] - capture_times[0];
        return capture_times[0] + position * step;
    }
    let floored = position.floor();
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let idx = floored as usize;
    let frac = position - floored;
    if idx + 1 < capture_times.len() {
        capture_times[idx] + frac * (capture_times[idx + 1] - capture_times[idx])
    } else if idx < capture_times.len() && frac.abs() <= 1e-15 {
        capture_times[idx]
    } else {
        let last = capture_times.len() - 1;
        let step = capture_times[last] - capture_times[last - 1];
        capture_times[last] + (position - as_float(last)) * step
    }
}

/// Playback speed over step `k -> k + 1`, matching `Unisono.Spec.World.speed`:
/// `(captured(y) - captured(x)) / (out_next - out_curr)` when the step is
/// continuous and `out_next > out_curr`, and `None` otherwise.
#[must_use]
pub fn step_speed(
    curr: Option<f64>,
    next: Option<f64>,
    out_curr: f64,
    out_next: f64,
    captured: impl Fn(f64) -> f64,
) -> Option<f64> {
    if !is_continuous(curr, next)
        || out_next <= out_curr
        || !out_next.is_finite()
        || !out_curr.is_finite()
    {
        return None;
    }
    let (Some(start_pos), Some(end_pos)) = (curr, next) else {
        return None;
    };
    Some((captured(end_pos) - captured(start_pos)) / (out_next - out_curr))
}

/// Roughness accrued between a continuous step (`first_speed` over
/// `[first_start, first_end]`) and the next continuous step (`next_speed` over
/// `[next_start, next_end]`), matching `Unisono.Spec.World.roughnessCost`:
/// `(next_speed - first_speed)^2 / (midpoint_next - midpoint_first)`.
#[must_use]
pub fn roughness_between(
    first_speed: f64,
    first_start: f64,
    first_end: f64,
    next_speed: f64,
    next_start: f64,
    next_end: f64,
) -> f64 {
    let first_mid = f64::midpoint(first_start, first_end);
    let next_mid = f64::midpoint(next_start, next_end);
    let dt = next_mid - first_mid;
    if dt > 0.0 && dt.is_finite() {
        let delta = next_speed - first_speed;
        (delta * delta) / dt
    } else {
        0.0
    }
}

/// True time at which playback `plays` (leaving at output sample times `out`)
/// first plays source frame `frame`, matching `Unisono.Spec.playTime`.
///
/// Linearly interpolates within the earliest continuous step `[x, y]` covering
/// `frame` (`x <= frame <= y`), or returns `None` if no continuous step covers
/// `frame`.
#[must_use]
pub fn play_time(out: &[f64], plays: &[Option<f64>], frame: u64) -> Option<f64> {
    let len = out.len().min(plays.len());
    if len < 2 {
        return None;
    }
    let frame_f = u64_to_f64(frame);
    for k in 0..(len - 1) {
        if is_continuous(plays[k], plays[k + 1])
            && let (Some(start_pos), Some(end_pos)) = (plays[k], plays[k + 1])
            && start_pos <= frame_f
            && frame_f <= end_pos
        {
            let frac = (frame_f - start_pos) / (end_pos - start_pos);
            return Some(out[k] + frac * (out[k + 1] - out[k]));
        }
    }
    None
}

/// Objective weights matching `Unisono.Spec.Weights`.
///
/// Low-latency mode sets `tracking = 0.0`; lip-sync mode sets `latency = 0.0`.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ObjectiveWeights {
    /// Weight on synchronization variance `sync_s2`, in `1/s^2`.
    pub sync: f64,
    /// Weight on mean latency `mean_latency_s`, in `1/s`.
    pub latency: f64,
    /// Weight on target-latency tracking MSE `tracking_s2`, in `1/s^2`.
    pub tracking: f64,
    /// Weight on continuous playback roughness `roughness_per_s2`, in `s^2`.
    pub roughness: f64,
    /// Weight on missed samples per second `missed_per_s`.
    pub missed: f64,
    /// Weight on discontinuities per second `discontinuities_per_s`, in `s`.
    pub discontinuities: f64,
}

impl ObjectiveWeights {
    /// All-zero weights.
    pub const ZERO: ObjectiveWeights = ObjectiveWeights {
        sync: 0.0,
        latency: 0.0,
        tracking: 0.0,
        roughness: 0.0,
        missed: 0.0,
        discontinuities: 0.0,
    };

    /// Weighted sum of the six canonical objectives of `report`.
    #[must_use]
    pub fn weighted_cost(self, report: &ObjectiveReport) -> f64 {
        self.sync * report.sync_s2
            + self.latency * report.mean_latency_s
            + self.tracking * report.tracking_s2
            + self.roughness * report.roughness_per_s2
            + self.missed * report.missed_per_s
            + self.discontinuities * report.discontinuities_per_s
    }
}

/// Canonical evaluation report implementing the six objectives of
/// `Unisono.Spec.Objectives` together with summary diagnostics.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ObjectiveReport {
    /// Long-run synchronization variance `Spec.World.sync`, in `s^2`.
    pub sync_s2: f64,
    /// Long-run mean latency `Spec.World.meanLatency`, in `s`.
    pub mean_latency_s: f64,
    /// Long-run squared target-latency error `Spec.World.tracking`, in `s^2`.
    pub tracking_s2: f64,
    /// Long-run continuous playback speed roughness `Spec.World.roughness`,
    /// in `s^-2`.
    pub roughness_per_s2: f64,
    /// Long-run missed output samples per second per speaker
    /// `Spec.World.missed`.
    pub missed_per_s: f64,
    /// Long-run playback discontinuities per second per speaker
    /// `Spec.World.discontinuities`.
    pub discontinuities_per_s: f64,
    /// RMS inter-speaker timing spread (`sqrt(sync_s2) * 1e6`), in
    /// microseconds.
    pub sync_rms_us: f64,
    /// Peak absolute pairwise play-time difference across speakers on
    /// in-window frames, in microseconds.
    pub max_abs_pair_spread_us: f64,
    /// Peak `|speed - 1.0|` across speakers and in-window continuous steps
    /// (checks `Unisono.Spec.Solution.WithinSpeed`).
    pub max_speed_deviation: f64,
    /// RMS change in cycle-average playback speed between adjacent continuous
    /// cycles (dimensionless).
    pub cycle_roughness_rms: f64,
    /// Weighted sum of the six canonical objectives under `ObjectiveWeights`.
    pub weighted_cost: f64,
}

/// Order-statistic summary of a finite sample slice.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Quantiles {
    /// Sample median (50th percentile).
    pub median: f64,
    /// Minimum value.
    pub min: f64,
    /// Maximum value.
    pub max: f64,
    /// Lower quartile (25th percentile).
    pub p25: f64,
    /// Upper quartile (75th percentile).
    pub p75: f64,
}

/// Computes `Quantiles` (`median`, `min`, `max`, `p25`, `p75`) using linear
/// interpolation between adjacent order statistics. Returns all zeros when
/// `values` is empty.
#[must_use]
pub fn quantiles(values: &[f64]) -> Quantiles {
    if values.is_empty() {
        return Quantiles::default();
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let last = sorted.len() - 1;
    let at = |prob: f64| -> f64 {
        let pos = prob * as_float(last);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let lo = pos.floor() as usize;
        let hi = (lo + 1).min(last);
        let frac = pos - as_float(lo);
        sorted[lo] + frac * (sorted[hi] - sorted[lo])
    };
    Quantiles {
        median: at(0.5),
        min: sorted[0],
        max: sorted[last],
        p25: at(0.25),
        p75: at(0.75),
    }
}

/// Complete sample-level trace of a simulation run for literal reference
/// evaluation via [`score_samples`].
#[derive(Clone, Debug)]
pub struct SampleTrace<'a> {
    /// True capture time `capture(n)` of each source frame `n`, in seconds.
    pub capture_times: &'a [f64],
    /// Target latency `target(n)` of each source frame `n`, in seconds.
    pub target_latencies: &'a [f64],
    /// True output times `out(r, k)` for each speaker `r`, in seconds.
    pub speaker_out_times: &'a [Vec<f64>],
    /// Effective played source positions `plays(r, k)` for each speaker `r`.
    pub speaker_plays: &'a [Vec<Option<f64>>],
    /// Start of the scoring window in true time (inclusive), in seconds.
    pub window_start: f64,
    /// End of the scoring window in true time (exclusive), in seconds.
    pub window_end: f64,
    /// Output samples per nominal playback cycle (for `cycle_roughness_rms`).
    pub cycle_frames: usize,
    /// Objective weights used for `weighted_cost`.
    pub weights: ObjectiveWeights,
}

/// Shared frame-level objective accumulator used by both [`score_samples`] and
/// [`ObjectiveRecorder`].
#[derive(Clone, Copy, Debug, Default)]
struct FrameAccum {
    sync_accrued: f64,
    latency_accrued: f64,
    tracking_accrued: f64,
    max_abs_pair_spread_s: f64,
}

impl FrameAccum {
    fn record(
        &mut self,
        capture_time: f64,
        next_capture_time: f64,
        target_latency: f64,
        play_times: &[Option<f64>],
        window_start: f64,
        window_end: f64,
    ) {
        if capture_time < window_start || capture_time >= window_end {
            return;
        }
        let r_count = play_times.len();
        if r_count == 0 {
            return;
        }
        let dt = (next_capture_time - capture_time).max(0.0);
        let r_f = as_float(r_count);

        let mut pair_sq_sum = 0.0;
        for first_idx in 0..r_count {
            if let Some(first_time) = play_times[first_idx] {
                for &second_opt in &play_times[(first_idx + 1)..] {
                    if let Some(second_time) = second_opt {
                        let diff = first_time - second_time;
                        pair_sq_sum += diff * diff;
                        self.max_abs_pair_spread_s = self.max_abs_pair_spread_s.max(diff.abs());
                    }
                }
            }
        }
        let sync_cost = pair_sq_sum / (r_f * r_f);

        let mut latency_sum = 0.0;
        let mut tracking_sum = 0.0;
        for &opt_time in play_times {
            if let Some(played_at) = opt_time {
                let lat = played_at - capture_time;
                latency_sum += lat.max(0.0);
                let err = lat - target_latency;
                tracking_sum += err * err;
            }
        }
        self.sync_accrued += sync_cost * dt;
        self.latency_accrued += (latency_sum / r_f) * dt;
        self.tracking_accrued += (tracking_sum / r_f) * dt;
    }
}

/// Shared output-side totals across speakers.
#[derive(Clone, Copy, Debug, Default)]
struct OutputTotals {
    roughness: f64,
    missed: u64,
    discontinuities: u64,
    max_speed_deviation: f64,
    cycle_dv_sq_sum: f64,
    cycle_dv_count: u64,
}

/// Shared per-speaker cycle-average speed-change accumulator used by both
/// [`score_samples`] and [`ObjectiveRecorder`].
#[derive(Clone, Copy, Debug, Default)]
struct CycleRoughnessAccum {
    curr_cycle: Option<(usize, f64, usize)>,
    prev_cycle: Option<(usize, f64)>,
    dv_sq_sum: f64,
    dv_count: u64,
}

impl CycleRoughnessAccum {
    fn push(&mut self, cycle_idx: usize, speed: f64) {
        match self.curr_cycle {
            Some((curr_idx, sum, count)) if curr_idx == cycle_idx => {
                self.curr_cycle = Some((curr_idx, sum + speed, count + 1));
            }
            Some((curr_idx, sum, count)) => {
                self.commit(curr_idx, sum / as_float(count));
                self.curr_cycle = Some((cycle_idx, speed, 1));
            }
            None => {
                self.curr_cycle = Some((cycle_idx, speed, 1));
            }
        }
    }

    fn commit(&mut self, cycle_idx: usize, mean_speed: f64) {
        if let Some((prev_idx, prev_speed)) = self.prev_cycle
            && prev_idx + 1 == cycle_idx
        {
            let delta = mean_speed - prev_speed;
            self.dv_sq_sum += delta * delta;
            self.dv_count += 1;
        }
        self.prev_cycle = Some((cycle_idx, mean_speed));
    }

    fn finish(&mut self) -> (f64, u64) {
        if let Some((curr_idx, sum, count)) = self.curr_cycle.take() {
            self.commit(curr_idx, sum / as_float(count));
        }
        (self.dv_sq_sum, self.dv_count)
    }
}

/// Builds an [`ObjectiveReport`] from finalized frame and output accumulators.
fn build_report(
    speakers: usize,
    horizon: f64,
    frames: FrameAccum,
    outputs: OutputTotals,
    weights: ObjectiveWeights,
) -> ObjectiveReport {
    if speakers == 0 || !(horizon > 0.0 && horizon.is_finite()) {
        return ObjectiveReport::default();
    }
    let denom = as_float(speakers) * horizon;
    let sync_s2 = frames.sync_accrued / horizon;
    let mean_latency_s = frames.latency_accrued / horizon;
    let tracking_s2 = frames.tracking_accrued / horizon;
    let roughness_per_s2 = outputs.roughness / denom;
    let missed_per_s = u64_to_f64(outputs.missed) / denom;
    let discontinuities_per_s = u64_to_f64(outputs.discontinuities) / denom;
    let cycle_roughness_rms = if outputs.cycle_dv_count > 0 {
        (outputs.cycle_dv_sq_sum / u64_to_f64(outputs.cycle_dv_count)).sqrt()
    } else {
        0.0
    };
    let mut report = ObjectiveReport {
        sync_s2,
        mean_latency_s,
        tracking_s2,
        roughness_per_s2,
        missed_per_s,
        discontinuities_per_s,
        sync_rms_us: sync_s2.max(0.0).sqrt() * 1e6,
        max_abs_pair_spread_us: frames.max_abs_pair_spread_s * 1e6,
        max_speed_deviation: outputs.max_speed_deviation,
        cycle_roughness_rms,
        weighted_cost: 0.0,
    };
    report.weighted_cost = weights.weighted_cost(&report);
    report
}

/// Computes exact first-cover play times per speaker across `0..num_frames`.
fn compute_first_play_times(
    speaker_out_times: &[Vec<f64>],
    speaker_plays: &[Vec<Option<f64>>],
    r_count: usize,
    num_frames: usize,
) -> Vec<Vec<Option<f64>>> {
    let mut table: Vec<Vec<Option<f64>>> = vec![vec![None; num_frames]; r_count];
    for r in 0..r_count {
        let out = &speaker_out_times[r];
        let plays = &speaker_plays[r];
        let len = out.len().min(plays.len());
        for k in 0..len.saturating_sub(1) {
            if is_continuous(plays[k], plays[k + 1])
                && let (Some(start_pos), Some(end_pos)) = (plays[k], plays[k + 1])
                && end_pos >= 0.0
            {
                let first_f = if start_pos > 0.0 {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    {
                        start_pos.ceil() as usize
                    }
                } else {
                    0
                };
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let last_f = (end_pos.floor() as usize).min(num_frames.saturating_sub(1));
                for (frame, slot) in table[r]
                    .iter_mut()
                    .enumerate()
                    .take(last_f.saturating_add(1).min(num_frames))
                    .skip(first_f)
                {
                    let frame_f = as_float(frame);
                    if start_pos <= frame_f && frame_f <= end_pos && slot.is_none() {
                        let frac = (frame_f - start_pos) / (end_pos - start_pos);
                        *slot = Some(out[k] + frac * (out[k + 1] - out[k]));
                    }
                }
            }
        }
    }
    table
}

/// Evaluates output-side objectives for one speaker in [`score_samples`].
fn score_speaker_outputs(
    trace: &SampleTrace<'_>,
    speaker: usize,
    cycle_frames: usize,
    totals: &mut OutputTotals,
) {
    let captured_fn = |pos: f64| captured_at(trace.capture_times, pos);
    let out = &trace.speaker_out_times[speaker];
    let plays = &trace.speaker_plays[speaker];
    let len = out.len().min(plays.len());
    let speeds: Vec<Option<f64>> = (0..len)
        .map(|k| {
            if k + 1 < len {
                step_speed(plays[k], plays[k + 1], out[k], out[k + 1], captured_fn)
            } else {
                None
            }
        })
        .collect();
    let mut cycle_accum = CycleRoughnessAccum::default();
    for k in 0..len {
        if out[k] < trace.window_start || out[k] >= trace.window_end {
            continue;
        }
        totals.missed += missed_at(&plays[..len], k);
        totals.discontinuities += discontinuity_at(&plays[..len], k);
        if let Some(speed_k) = speeds[k] {
            totals.max_speed_deviation = totals.max_speed_deviation.max((speed_k - 1.0).abs());
            cycle_accum.push(k / cycle_frames, speed_k);
            if let Some((next_idx, next_speed)) =
                ((k + 1)..len).find_map(|idx| speeds[idx].map(|val| (idx, val)))
            {
                totals.roughness += roughness_between(
                    speed_k,
                    out[k],
                    out[k + 1],
                    next_speed,
                    out[next_idx],
                    out[next_idx + 1],
                );
            }
        }
    }
    let (dv_sq, dv_cnt) = cycle_accum.finish();
    totals.cycle_dv_sq_sum += dv_sq;
    totals.cycle_dv_count += dv_cnt;
}

/// Literal reference scorer evaluating all six canonical objectives of
/// `Unisono.Spec.Objectives` on complete sample arrays.
#[must_use]
pub fn score_samples(trace: &SampleTrace<'_>) -> ObjectiveReport {
    let r_count = trace.speaker_out_times.len().min(trace.speaker_plays.len());
    let horizon = trace.window_end - trace.window_start;
    if r_count == 0 || !(horizon > 0.0 && horizon.is_finite()) {
        return ObjectiveReport::default();
    }
    let cycle_frames = trace.cycle_frames.max(1);
    let num_frames = trace.capture_times.len().saturating_sub(1);
    let first_play_times = compute_first_play_times(
        trace.speaker_out_times,
        trace.speaker_plays,
        r_count,
        num_frames,
    );

    let mut frame_accum = FrameAccum::default();
    let mut row_buf = vec![None; r_count];
    for frame in 0..num_frames {
        for (dst, sp_times) in row_buf.iter_mut().zip(&first_play_times) {
            *dst = sp_times[frame];
        }
        let target = trace.target_latencies.get(frame).copied().unwrap_or(0.0);
        frame_accum.record(
            trace.capture_times[frame],
            trace.capture_times[frame + 1],
            target,
            &row_buf,
            trace.window_start,
            trace.window_end,
        );
    }

    let mut outputs = OutputTotals::default();
    for speaker in 0..r_count {
        score_speaker_outputs(trace, speaker, cycle_frames, &mut outputs);
    }

    build_report(r_count, horizon, frame_accum, outputs, trace.weights)
}

/// Stored metadata for one buffered source frame inside [`ObjectiveRecorder`].
#[derive(Clone, Debug)]
struct FrameRecord {
    capture_time: f64,
    target_latency: f64,
    play_times: Vec<Option<f64>>,
}

/// Most recent continuous step seen on a speaker (for cross-break roughness).
#[derive(Clone, Copy, Debug)]
struct ContinuousStep {
    out_start: f64,
    out_end: f64,
    speed: f64,
    in_window: bool,
}

/// One continuous playback transition `prev_idx -> prev_idx + 1` on a speaker.
#[derive(Clone, Copy, Debug)]
struct StepTransition {
    speaker: usize,
    prev_idx: usize,
    prev_out: f64,
    out_time_s: f64,
    start_pos: f64,
    end_pos: f64,
    in_window_prev: bool,
}

/// Streaming per-speaker output-side accumulators inside [`ObjectiveRecorder`].
#[derive(Clone, Debug, Default)]
struct SpeakerState {
    sample_count: usize,
    prev_sample: Option<(f64, Option<f64>)>,
    last_some: Option<(usize, f64)>,
    prev_continuous: Option<ContinuousStep>,
    cycle_accum: CycleRoughnessAccum,
    missed_total: u64,
    discontinuities_total: u64,
    roughness_total: f64,
    max_speed_deviation: f64,
}

/// Default number of source frames retained in [`ObjectiveRecorder`] before
/// retiring the oldest frame (~1.36 s at 48 kHz).
const DEFAULT_MAX_BUFFERED_FRAMES: usize = 65_536;

/// Compact streaming evaluator of all six canonical objectives in
/// `Unisono.Spec.Objectives`.
///
/// Produces the same results as [`score_samples`] while keeping per-speaker
/// output state in `O(1)` memory and retiring old source frame records once the
/// rolling buffer exceeds `max_buffered_frames`.
#[derive(Clone, Debug)]
pub struct ObjectiveRecorder {
    window_start: f64,
    window_end: f64,
    cycle_frames: usize,
    weights: ObjectiveWeights,
    max_buffered_frames: usize,
    base_frame: u64,
    last_capture_dt: f64,
    frames: VecDeque<FrameRecord>,
    frame_accum: FrameAccum,
    speakers: Vec<SpeakerState>,
}

impl ObjectiveRecorder {
    /// Creates a streaming recorder for `speakers` speakers over the scoring
    /// window `[window_start, window_end)` in true-time seconds.
    #[must_use]
    pub fn new(
        speakers: usize,
        window_start: f64,
        window_end: f64,
        cycle_frames: usize,
        weights: ObjectiveWeights,
    ) -> ObjectiveRecorder {
        ObjectiveRecorder {
            window_start,
            window_end,
            cycle_frames: cycle_frames.max(1),
            weights,
            max_buffered_frames: DEFAULT_MAX_BUFFERED_FRAMES,
            base_frame: 0,
            last_capture_dt: 1.0 / 48_000.0,
            frames: VecDeque::new(),
            frame_accum: FrameAccum::default(),
            speakers: vec![SpeakerState::default(); speakers],
        }
    }

    /// Overrides the rolling source-frame buffer size before old frames are
    /// scored and retired.
    #[must_use]
    pub fn with_max_buffered_frames(mut self, max_frames: usize) -> ObjectiveRecorder {
        self.max_buffered_frames = max_frames.max(2);
        self
    }

    /// Records the capture of the next consecutive source frame at true time
    /// `capture_time_s` with target latency `target_latency_s`.
    pub fn record_capture_frame(&mut self, capture_time_s: f64, target_latency_s: f64) {
        if let Some(prev) = self.frames.back() {
            let dt = capture_time_s - prev.capture_time;
            if dt > 0.0 && dt.is_finite() {
                self.last_capture_dt = dt;
            }
        }
        self.frames.push_back(FrameRecord {
            capture_time: capture_time_s,
            target_latency: target_latency_s,
            play_times: vec![None; self.speakers.len()],
        });
        while self.frames.len() > self.max_buffered_frames {
            self.retire_oldest_frame();
        }
    }

    fn retire_oldest_frame(&mut self) {
        if self.frames.len() < 2 {
            return;
        }
        let next_cap = self.frames[1].capture_time;
        if let Some(record) = self.frames.pop_front() {
            self.base_frame += 1;
            self.frame_accum.record(
                record.capture_time,
                next_cap,
                record.target_latency,
                &record.play_times,
                self.window_start,
                self.window_end,
            );
        }
    }

    fn captured_position(&self, position: f64) -> f64 {
        if self.frames.is_empty() || !position.is_finite() {
            return 0.0;
        }
        let base_f = u64_to_f64(self.base_frame);
        if position < base_f {
            return self.frames[0].capture_time + (position - base_f) * self.last_capture_dt;
        }
        let floored = position.floor();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let frame_u64 = floored as u64;
        let frac = position - floored;
        let rel = usize::try_from(frame_u64.saturating_sub(self.base_frame)).unwrap_or(usize::MAX);
        if rel + 1 < self.frames.len() {
            let start_cap = self.frames[rel].capture_time;
            let end_cap = self.frames[rel + 1].capture_time;
            start_cap + frac * (end_cap - start_cap)
        } else if rel < self.frames.len() && frac.abs() <= 1e-15 {
            self.frames[rel].capture_time
        } else {
            let last_idx = self.frames.len() - 1;
            let last_frame = base_f + as_float(last_idx);
            let step = if last_idx >= 1 {
                self.frames[last_idx].capture_time - self.frames[last_idx - 1].capture_time
            } else {
                self.last_capture_dt
            };
            self.frames[last_idx].capture_time + (position - last_frame) * step
        }
    }

    fn record_first_play_time(&mut self, speaker: usize, frame: u64, played_at: f64) {
        if frame < self.base_frame {
            return;
        }
        let rel = usize::try_from(frame - self.base_frame).unwrap_or(usize::MAX);
        if let Some(rec) = self.frames.get_mut(rel)
            && let Some(slot) = rec.play_times.get_mut(speaker)
            && slot.is_none()
        {
            *slot = Some(played_at);
        }
    }

    fn record_continuous_step(&mut self, step: StepTransition) {
        let cap_start = self.captured_position(step.start_pos);
        let cap_end = self.captured_position(step.end_pos);
        let speed = (cap_end - cap_start) / (step.out_time_s - step.prev_out);

        let sp = &mut self.speakers[step.speaker];
        if let Some(prev_step) = sp.prev_continuous
            && prev_step.in_window
        {
            sp.roughness_total += roughness_between(
                prev_step.speed,
                prev_step.out_start,
                prev_step.out_end,
                speed,
                step.prev_out,
                step.out_time_s,
            );
        }
        sp.prev_continuous = Some(ContinuousStep {
            out_start: step.prev_out,
            out_end: step.out_time_s,
            speed,
            in_window: step.in_window_prev,
        });
        if step.in_window_prev {
            sp.max_speed_deviation = sp.max_speed_deviation.max((speed - 1.0).abs());
            sp.cycle_accum
                .push(step.prev_idx / self.cycle_frames, speed);
        }

        if step.end_pos >= 0.0 {
            let first_frame = if step.start_pos > 0.0 {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                {
                    step.start_pos.ceil() as u64
                }
            } else {
                0
            };
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let last_frame = step.end_pos.floor() as u64;
            for frame in first_frame..=last_frame {
                let frame_f = u64_to_f64(frame);
                if step.start_pos <= frame_f && frame_f <= step.end_pos {
                    let frac = (frame_f - step.start_pos) / (step.end_pos - step.start_pos);
                    let played_at = step.prev_out + frac * (step.out_time_s - step.prev_out);
                    self.record_first_play_time(step.speaker, frame, played_at);
                }
            }
        }
    }

    /// Records one playback output sample for `speaker` leaving at true time
    /// `out_time_s` with already-filtered effective source position
    /// `effective_play`.
    pub fn record_playback_sample(
        &mut self,
        speaker: usize,
        out_time_s: f64,
        effective_play: Option<f64>,
    ) {
        if speaker >= self.speakers.len() {
            return;
        }
        let sample_idx = self.speakers[speaker].sample_count;
        let in_window_curr = out_time_s >= self.window_start && out_time_s < self.window_end;

        let missed = missed_at_step(effective_play, sample_idx, self.speakers[speaker].last_some);
        if in_window_curr {
            self.speakers[speaker].missed_total += missed;
        }
        if let Some(pos) = effective_play {
            self.speakers[speaker].last_some = Some((sample_idx, pos));
        }

        if let Some((prev_out, prev_play)) = self.speakers[speaker].prev_sample {
            let prev_idx = sample_idx - 1;
            let in_window_prev = prev_out >= self.window_start && prev_out < self.window_end;
            let continuous = is_continuous(prev_play, effective_play);

            if in_window_prev && prev_play.is_some() && !continuous {
                self.speakers[speaker].discontinuities_total += 1;
            }
            if continuous
                && out_time_s > prev_out
                && let (Some(start_pos), Some(end_pos)) = (prev_play, effective_play)
            {
                self.record_continuous_step(StepTransition {
                    speaker,
                    prev_idx,
                    prev_out,
                    out_time_s,
                    start_pos,
                    end_pos,
                    in_window_prev,
                });
            }
        }

        let sp = &mut self.speakers[speaker];
        sp.prev_sample = Some((out_time_s, effective_play));
        sp.sample_count += 1;
    }

    /// Records one playback output sample for `speaker`, first applying the
    /// exact `Unisono.Spec.playable` lookahead filter against `is_held`.
    pub fn record_playback_sample_checked(
        &mut self,
        speaker: usize,
        out_time_s: f64,
        chosen_play: Option<f64>,
        lookahead: usize,
        is_held: impl Fn(u64) -> bool,
    ) {
        let effective = playable(chosen_play, lookahead, is_held);
        self.record_playback_sample(speaker, out_time_s, effective);
    }

    /// Finalizes all buffered frames and open playback cycles, returning the
    /// canonical [`ObjectiveReport`].
    #[must_use]
    pub fn finish(mut self) -> ObjectiveReport {
        while self.frames.len() >= 2 {
            self.retire_oldest_frame();
        }
        let mut outputs = OutputTotals::default();
        for sp in &mut self.speakers {
            outputs.roughness += sp.roughness_total;
            outputs.missed += sp.missed_total;
            outputs.discontinuities += sp.discontinuities_total;
            outputs.max_speed_deviation = outputs.max_speed_deviation.max(sp.max_speed_deviation);
            let (dv_sq, dv_cnt) = sp.cycle_accum.finish();
            outputs.cycle_dv_sq_sum += dv_sq;
            outputs.cycle_dv_count += dv_cnt;
        }

        build_report(
            self.speakers.len(),
            self.window_end - self.window_start,
            self.frame_accum,
            outputs,
            self.weights,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ObjectiveRecorder, ObjectiveReport, ObjectiveWeights, Quantiles, SampleTrace,
        discontinuity_at, is_continuous, is_playable, missed_at, play_time, playable, quantiles,
        roughness_between, score_samples, step_speed,
    };

    const WEIGHTS: ObjectiveWeights = ObjectiveWeights {
        sync: 1e6,
        latency: 10.0,
        tracking: 1e4,
        roughness: 1e2,
        missed: 5.0,
        discontinuities: 100.0,
    };

    fn assert_reports_match(streaming: &ObjectiveReport, reference: &ObjectiveReport, label: &str) {
        let fields = [
            ("sync_s2", streaming.sync_s2, reference.sync_s2),
            (
                "mean_latency_s",
                streaming.mean_latency_s,
                reference.mean_latency_s,
            ),
            ("tracking_s2", streaming.tracking_s2, reference.tracking_s2),
            (
                "roughness_per_s2",
                streaming.roughness_per_s2,
                reference.roughness_per_s2,
            ),
            (
                "missed_per_s",
                streaming.missed_per_s,
                reference.missed_per_s,
            ),
            (
                "discontinuities_per_s",
                streaming.discontinuities_per_s,
                reference.discontinuities_per_s,
            ),
            ("sync_rms_us", streaming.sync_rms_us, reference.sync_rms_us),
            (
                "max_abs_pair_spread_us",
                streaming.max_abs_pair_spread_us,
                reference.max_abs_pair_spread_us,
            ),
            (
                "max_speed_deviation",
                streaming.max_speed_deviation,
                reference.max_speed_deviation,
            ),
            (
                "cycle_roughness_rms",
                streaming.cycle_roughness_rms,
                reference.cycle_roughness_rms,
            ),
            (
                "weighted_cost",
                streaming.weighted_cost,
                reference.weighted_cost,
            ),
        ];
        for (name, got, expected) in fields {
            let tol = 1e-10 * (1.0 + expected.abs());
            assert!(
                (got - expected).abs() <= tol,
                "{label}: field `{name}` mismatch: recorder={got:.12e} vs reference={expected:.12e}"
            );
        }
    }

    fn run_both(trace: &SampleTrace<'_>) -> (ObjectiveReport, ObjectiveReport) {
        let reference = score_samples(trace);
        let mut recorder = ObjectiveRecorder::new(
            trace.speaker_out_times.len(),
            trace.window_start,
            trace.window_end,
            trace.cycle_frames,
            trace.weights,
        );
        for (idx, &cap) in trace.capture_times.iter().enumerate() {
            let target = trace.target_latencies.get(idx).copied().unwrap_or(0.0);
            recorder.record_capture_frame(cap, target);
        }
        for r in 0..trace.speaker_out_times.len() {
            for (&out_t, &play) in trace.speaker_out_times[r]
                .iter()
                .zip(&trace.speaker_plays[r])
            {
                recorder.record_playback_sample(r, out_t, play);
            }
        }
        (recorder.finish(), reference)
    }

    #[test]
    fn ideal_zero_cost_trajectory_matches_exact_zero_on_all_error_objectives() {
        let dt = 0.001;
        let target_lat = 0.02;
        let n = 400_usize;
        let capture: Vec<f64> = (0..=n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    k as f64 * dt
                }
            })
            .collect();
        let targets = vec![target_lat; n + 1];
        let outs: Vec<f64> = (0..=n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    target_lat + k as f64 * dt
                }
            })
            .collect();
        let plays: Vec<Option<f64>> = (0..=n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                Some(k as f64)
            })
            .collect();
        let speaker_outs = [outs.clone(), outs];
        let speaker_plays = [plays.clone(), plays];
        let trace = SampleTrace {
            capture_times: &capture,
            target_latencies: &targets,
            speaker_out_times: &speaker_outs,
            speaker_plays: &speaker_plays,
            window_start: 0.0505,
            window_end: 0.3505,
            cycle_frames: 16,
            weights: ObjectiveWeights {
                latency: 0.0,
                ..WEIGHTS
            },
        };

        let (streaming, reference) = run_both(&trace);
        assert_reports_match(&streaming, &reference, "ideal");
        assert!(streaming.sync_s2.abs() < 1e-18);
        assert!((streaming.mean_latency_s - target_lat).abs() < 1e-12);
        assert!(streaming.tracking_s2.abs() < 1e-18);
        assert!(streaming.roughness_per_s2.abs() < 1e-18);
        assert!(streaming.missed_per_s.abs() < 1e-18);
        assert!(streaming.discontinuities_per_s.abs() < 1e-18);
        assert!(streaming.max_speed_deviation.abs() < 1e-12);
        assert!(streaming.cycle_roughness_rms.abs() < 1e-12);
        assert!(streaming.weighted_cost.abs() < 1e-12);
    }

    #[test]
    fn speed_ramp_and_constant_inter_speaker_offset_match_analytical_values() {
        let dt = 0.001;
        let n = 500_usize;
        let capture: Vec<f64> = (0..=n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    k as f64 * dt
                }
            })
            .collect();
        let targets = vec![0.02; n + 1];

        // Speaker 0 runs a linear speed ramp `v(t) = 1.0 + accel * t` with
        // `accel = 0.02 s^-1`, so `roughness = accel^2 = 4e-4 s^-2`.
        // Speaker 1 runs the exact same ramp shifted 100 us later, so
        // `sync_s2 = (100e-6)^2 / 4 = 2.5e-9 s^2` (`sync_rms_us = 50 us`).
        let accel = 0.02;
        let shift = 100e-6;
        let mut out0 = Vec::with_capacity(n + 1);
        let mut out1 = Vec::with_capacity(n + 1);
        let mut play0 = Vec::with_capacity(n + 1);
        let mut pos = 0.0_f64;
        for k in 0..=n {
            #[allow(clippy::cast_precision_loss)]
            let t = k as f64 * dt;
            out0.push(0.02 + t);
            out1.push(0.02 + shift + t);
            play0.push(Some(pos));
            let speed_k = 1.0 + accel * (t + 0.5 * dt);
            pos += speed_k;
        }
        let speaker_outs = [out0, out1];
        let speaker_plays = [play0.clone(), play0];
        let trace = SampleTrace {
            capture_times: &capture,
            target_latencies: &targets,
            speaker_out_times: &speaker_outs,
            speaker_plays: &speaker_plays,
            window_start: 0.0495,
            window_end: 0.3995,
            cycle_frames: 10,
            weights: WEIGHTS,
        };
        let (streaming, reference) = run_both(&trace);
        assert_reports_match(&streaming, &reference, "speed_ramp");
        assert!(
            (streaming.sync_rms_us - 50.0).abs() < 0.2,
            "sync_rms_us={}",
            streaming.sync_rms_us
        );
        assert!(
            (streaming.max_abs_pair_spread_us - 100.0).abs() < 0.2,
            "max_abs_pair_spread_us={}",
            streaming.max_abs_pair_spread_us
        );
        assert!(
            (streaming.roughness_per_s2 - accel * accel).abs() < 1e-6,
            "roughness={}",
            streaming.roughness_per_s2
        );
        assert!(
            (streaming.cycle_roughness_rms - accel * 10.0 * dt).abs() < 1e-7,
            "cycle_roughness_rms={}",
            streaming.cycle_roughness_rms
        );
    }

    #[test]
    fn pauses_forward_skips_and_backward_replays_match_reference_and_first_cover() {
        let dt = 0.001;
        let n = 200_usize;
        let capture: Vec<f64> = (0..=n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    k as f64 * dt
                }
            })
            .collect();
        let targets = vec![0.02; n + 1];
        let outs: Vec<f64> = (0..n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    0.02 + k as f64 * dt
                }
            })
            .collect();

        // Speaker 0: continuous -> 5-sample None gap -> forward skip (+4 extra)
        // at speed 1.05 (exercises cross-break roughness) -> backward replay by
        // ~9 frames (exercises first-cover `playTime`) -> forward jump by 15.
        let mut play0: Vec<Option<f64>> = Vec::with_capacity(n);
        for k in 0..40_i32 {
            play0.push(Some(f64::from(k)));
        }
        play0.extend(std::iter::repeat_n(None, 5));
        let mut p = 49.0;
        for _ in 45..80 {
            play0.push(Some(p));
            p += 1.05;
        }
        let mut p_back = p - 10.0;
        for _ in 80..120 {
            play0.push(Some(p_back));
            p_back += 1.0;
        }
        let mut p_fwd = p_back + 15.0;
        for _ in 120..n {
            play0.push(Some(p_fwd));
            p_fwd += 1.0;
        }
        let play1: Vec<Option<f64>> = (0..n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                Some(k as f64)
            })
            .collect();

        assert!(is_continuous(play0[38], play0[39]));
        assert!(!is_continuous(play0[39], play0[40]));
        assert_eq!(discontinuity_at(&play0, 39), 1);
        assert_eq!(discontinuity_at(&play0, 40), 0);
        assert_eq!(missed_at(&play0, 40), 1);
        assert_eq!(missed_at(&play0, 45), 4);
        assert_eq!(discontinuity_at(&play0, 79), 1);
        // `play0[79] = 84.7`, `play0[80] = 75.75` -> `floor(1 - (-8.95)) = 9`.
        assert_eq!(missed_at(&play0, 80), 9);

        // First-cover `play_time` for frame 78 must return its initial cover
        // before the backward replay at k=80 (`< 0.100 s`).
        let pt_78 = play_time(&outs, &play0, 78).expect("frame 78 covered");
        assert!(pt_78 < 0.02 + 0.080, "expected first cover, got {pt_78}");

        // Cross-break roughness pairs step 38 (speed 1.0) with step 45 (speed 1.05).
        let v38 = step_speed(play0[38], play0[39], outs[38], outs[39], |x| x * dt).expect("v38");
        let v45 = step_speed(play0[45], play0[46], outs[45], outs[46], |x| x * dt).expect("v45");
        let cross_r = roughness_between(v38, outs[38], outs[39], v45, outs[45], outs[46]);
        let expected_cross = (0.05_f64).powi(2) / (7.0 * dt);
        assert!((cross_r - expected_cross).abs() < 1e-9);

        let speaker_outs = [outs.clone(), outs];
        let speaker_plays = [play0, play1];
        let trace = SampleTrace {
            capture_times: &capture,
            target_latencies: &targets,
            speaker_out_times: &speaker_outs,
            speaker_plays: &speaker_plays,
            window_start: 0.0305,
            window_end: 0.1905,
            cycle_frames: 8,
            weights: WEIGHTS,
        };
        let (streaming, reference) = run_both(&trace);
        assert_reports_match(&streaming, &reference, "pauses_skips_replays");
        assert!(streaming.discontinuities_per_s > 0.0);
        assert!(streaming.missed_per_s > 0.0);
        assert!(streaming.roughness_per_s2 > 0.0);
    }

    #[test]
    fn lookahead_playability_filter_and_rolling_retirement_match_reference() {
        assert!(is_playable(999.98, 1, |f| f == 999 || f == 1_000));
        assert!(!is_playable(999.98, 1, |f| f == 999));
        assert!(is_playable(999.0, 1, |f| f == 999));
        assert!(!is_playable(-0.001, 1, |_| true));
        assert!(
            playable(Some(5.2), 2, |f| (4..=7).contains(&f))
                .is_some_and(|val| (val - 5.2).abs() < 1e-12)
        );
        assert!(playable(Some(5.2), 2, |f| (4..=6).contains(&f)).is_none());

        let dt = 0.001;
        let n = 100_usize;
        let capture: Vec<f64> = (0..=n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    k as f64 * dt
                }
            })
            .collect();
        let targets = vec![0.01; n + 1];
        let outs: Vec<f64> = (0..n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                {
                    0.01 + k as f64 * dt
                }
            })
            .collect();
        let chosen: Vec<Option<f64>> = (0..n)
            .map(|k| {
                #[allow(clippy::cast_precision_loss)]
                Some(k as f64 + 0.25)
            })
            .collect();
        let is_held = |frame: u64| frame != 50;
        let filtered: Vec<Option<f64>> = chosen
            .iter()
            .map(|&pos| playable(pos, 2, is_held))
            .collect();
        assert!(filtered[48].is_none());
        assert!(filtered[49].is_none());
        assert!(filtered[50].is_none());
        assert!(filtered[51].is_none());
        assert!(filtered[47].is_some());
        assert!(filtered[52].is_some());

        let reference = score_samples(&SampleTrace {
            capture_times: &capture,
            target_latencies: &targets,
            speaker_out_times: std::slice::from_ref(&outs),
            speaker_plays: &[filtered],
            window_start: 0.0205,
            window_end: 0.0905,
            cycle_frames: 8,
            weights: WEIGHTS,
        });

        // Interleave capture and playback chronologically with a small rolling
        // buffer (`max_buffered_frames = 32`) so early frames retire mid-run.
        let mut recorder =
            ObjectiveRecorder::new(1, 0.0205, 0.0905, 8, WEIGHTS).with_max_buffered_frames(32);
        let mut played_so_far = 0_usize;
        for cap_idx in 0..=n {
            recorder.record_capture_frame(capture[cap_idx], targets[cap_idx]);
            // Playback sample `j` needs frames up to `j + 2`.
            while played_so_far < n && played_so_far + 2 <= cap_idx {
                recorder.record_playback_sample_checked(
                    0,
                    outs[played_so_far],
                    chosen[played_so_far],
                    2,
                    is_held,
                );
                played_so_far += 1;
            }
        }
        while played_so_far < n {
            recorder.record_playback_sample_checked(
                0,
                outs[played_so_far],
                chosen[played_so_far],
                2,
                is_held,
            );
            played_so_far += 1;
        }
        let streaming = recorder.finish();
        assert_reports_match(&streaming, &reference, "lookahead_and_retirement");
        assert!(streaming.missed_per_s > 0.0);
        assert!(streaming.discontinuities_per_s > 0.0);
    }

    #[test]
    fn quantiles_computes_exact_order_statistics() {
        assert_eq!(quantiles(&[]), Quantiles::default());
        let q = quantiles(&[10.0, 2.0, 8.0, 4.0, 6.0]);
        assert!((q.min - 2.0).abs() < 1e-12);
        assert!((q.p25 - 4.0).abs() < 1e-12);
        assert!((q.median - 6.0).abs() < 1e-12);
        assert!((q.p75 - 8.0).abs() < 1e-12);
        assert!((q.max - 10.0).abs() < 1e-12);
    }
}
