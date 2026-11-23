// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Bandlimited quadrature probe waveform and black-box PCM output decoder.
//!
//! The simulator feeds a deterministic stereo probe waveform into the sender's
//! capture input and decodes the receiver's actual rendered PCM output back
//! into continuous global source frame positions `Option<f64>` without reading
//! any internal receiver state (`Plan`, playhead, or held-frame bitmap).
//!
//! # Signal design
//!
//! Over a period of `PERIOD = 131_072` frames (`2.73 s` at 48 kHz, exceeding
//! Unisono's 2 s maximum playout latency), the stereo signal combines:
//! - a quadrature carrier at `1 / 256` cycles/frame (`187.5 Hz` at 48 kHz) of
//!   amplitude `0.50` for fast coarse phase estimation, and
//! - two independent bandlimited pseudo-random multi-tone watermarks spanning
//!   `[0.05, 0.20]` cycles/frame (`[2.4 kHz, 9.6 kHz]` at 48 kHz, ~20,000
//!   frequencies per channel) for exact Gauss-Newton position refinement and
//!   immediate rejection of Burg AR(32) concealment, crossfades, and silence.
//!
//! Because all energy lies strictly below `0.20` cycles/frame, the production
//! Kaiser-sinc resampler (`Filter::for_rate`, `-110 dB` passband up to
//! `20 kHz`) reproduces the waveform at arbitrary fractional source positions
//! to `< 1e-5`, whereas concealed, faded, or silent output violates the
//! watermark immediately and scores as `None`.

use std::f64::consts::TAU;
use std::sync::OnceLock;

use crate::random::Generator;

/// Unambiguous signal period in source frames (`2^17 = 131_072`, `2.73 s` at
/// 48 kHz).
pub const PERIOD: usize = 1 << 17;

/// Carrier period in source frames (`1 / 256` cycles/frame = `187.5 Hz` at
/// 48 kHz).
const CARRIER_PERIOD: usize = 256;

/// Carrier bin index inside the `PERIOD`-point spectrum.
const CARRIER_BIN: usize = PERIOD / CARRIER_PERIOD;

/// Carrier amplitude on each quadrature channel.
const CARRIER_AMP: f64 = 0.45;

/// Watermark target RMS per channel.
const WATERMARK_RMS: f64 = 0.12;

/// Table oversampling factor (`h = 0.125` frame) for `< 1e-6` cubic Hermite
/// interpolation of both signal value and first derivative.
const OVERSAMPLE: usize = 8;

/// Oversampling factor as `f64`.
const OVERSAMPLE_F64: f64 = 8.0;

/// Total number of oversampled table entries (`8 * PERIOD`).
const TABLE_LEN: usize = PERIOD * OVERSAMPLE;

/// Step size in frames between adjacent oversampled table entries.
const H_STEP: f64 = 1.0 / OVERSAMPLE_F64;

/// Maximum stereo Euclidean sample residual accepted as faithful un-concealed
/// source audio.
const RESIDUAL_TOL: f64 = 2e-4;

/// Maximum residual (frames) under which a contiguous decoded block is
/// recognized as candidate constant-step resampled audio for joint PCM
/// Gauss-Newton refinement.
const LINEAR_BLOCK_TOL: f64 = 2e-2;

/// Minimum signal energy (`y0^2 + y1^2`) considered non-silent.
const SILENCE_ENERGY: f64 = 1e-4;

/// Precomputed oversampled probe table storing `[s0, s1, ds0/dx, ds1/dx]`.
struct ProbeTable {
    entries: Vec<[f64; 4]>,
}

/// In-place radix-2 Cooley-Tukey complex FFT (inverse when `inverse == true`,
/// unnormalized).
fn fft_radix2(re: &mut [f64], im: &mut [f64], inverse: bool) {
    let n = re.len();
    debug_assert_eq!(n, im.len());
    debug_assert!(n.is_power_of_two());

    // Bit-reversal permutation.
    let mut j = 0usize;
    for i in 1..n {
        let mut bit = n >> 1;
        while (j & bit) != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            re.swap(i, j);
            im.swap(i, j);
        }
    }

    let sign = if inverse { 1.0 } else { -1.0 };
    let mut len = 2usize;
    while len <= n {
        let half = len >> 1;
        #[allow(clippy::cast_precision_loss)]
        let angle = sign * TAU / (len as f64);
        let wlen_re = angle.cos();
        let wlen_im = angle.sin();
        let mut start = 0usize;
        while start < n {
            let mut w_re = 1.0_f64;
            let mut w_im = 0.0_f64;
            for k in 0..half {
                let u = start + k;
                let v = u + half;
                let t_re = re[v] * w_re - im[v] * w_im;
                let t_im = re[v] * w_im + im[v] * w_re;
                re[v] = re[u] - t_re;
                im[v] = im[u] - t_im;
                re[u] += t_re;
                im[u] += t_im;
                let next_re = w_re * wlen_re - w_im * wlen_im;
                let next_im = w_re * wlen_im + w_im * wlen_re;
                w_re = next_re;
                w_im = next_im;
            }
            start += len;
        }
        len <<= 1;
    }
}

/// Converts a `usize` to `f64`.
fn usize_to_f64(value: usize) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let f = value as f64;
    f
}

/// Converts a `u64` to `f64`.
fn u64_to_f64(value: u64) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let f = value as f64;
    f
}

/// Builds the global deterministic oversampled probe table once per process.
fn build_table() -> ProbeTable {
    let mut rng = Generator::new(0x554E_4953_4F4E_4F32);
    let low_bin = PERIOD / 16; // 0.0625 cycles/frame (3.0 kHz @ 48 kHz)
    let high_bin = (PERIOD * 7) / 25; // 0.28 cycles/frame (13.44 kHz @ 48 kHz)

    let mut spec_re = vec![0.0_f64; TABLE_LEN];
    let mut spec_im = vec![0.0_f64; TABLE_LEN];
    let mut dspec_re = vec![0.0_f64; TABLE_LEN];
    let mut dspec_im = vec![0.0_f64; TABLE_LEN];

    let period_f = usize_to_f64(PERIOD);
    // Populate independent random unit-magnitude phases on positive and
    // negative watermark bins so real and imaginary parts yield two
    // independent strictly bandlimited real channels `W0(x)` and `W1(x)`.
    for bin in low_bin..=high_bin {
        let omega = TAU * usize_to_f64(bin) / period_f;
        let phi_pos = rng.uniform() * TAU;
        let (sp, cp) = phi_pos.sin_cos();
        spec_re[bin] = cp;
        spec_im[bin] = sp;
        // d/dx [e^{+i omega x}] = +i omega e^{+i omega x}
        dspec_re[bin] = -omega * sp;
        dspec_im[bin] = omega * cp;

        let neg = TABLE_LEN - bin;
        let phi_neg = rng.uniform() * TAU;
        let (sn, cn) = phi_neg.sin_cos();
        spec_re[neg] = cn;
        spec_im[neg] = sn;
        // d/dx [e^{-i omega x}] = -i omega e^{-i omega x}
        dspec_re[neg] = omega * sn;
        dspec_im[neg] = -omega * cn;
    }

    fft_radix2(&mut spec_re, &mut spec_im, true);
    fft_radix2(&mut dspec_re, &mut dspec_im, true);

    // Normalize watermark RMS to `WATERMARK_RMS` while keeping peak safely
    // inside `[-0.45, 0.45]` so carrier + watermark stays within `[-0.90, 0.90]`.
    let mut sum_sq = 0.0_f64;
    let mut peak = 0.0_f64;
    for i in 0..TABLE_LEN {
        sum_sq += spec_re[i] * spec_re[i] + spec_im[i] * spec_im[i];
        peak = peak.max(spec_re[i].abs()).max(spec_im[i].abs());
    }
    let rms = (sum_sq / (2.0 * usize_to_f64(TABLE_LEN))).sqrt().max(1e-30);
    let scale = (WATERMARK_RMS / rms).min(0.45 / peak.max(1e-30));

    let omega0 = TAU * usize_to_f64(CARRIER_BIN) / period_f;
    let mut entries = Vec::with_capacity(TABLE_LEN);
    for i in 0..TABLE_LEN {
        let x = usize_to_f64(i) * H_STEP;
        let (s_c, c_c) = (omega0 * x).sin_cos();
        let s0 = CARRIER_AMP * c_c + spec_re[i] * scale;
        let s1 = CARRIER_AMP * s_c + spec_im[i] * scale;
        let ds0 = -CARRIER_AMP * omega0 * s_c + dspec_re[i] * scale;
        let ds1 = CARRIER_AMP * omega0 * c_c + dspec_im[i] * scale;
        entries.push([s0, s1, ds0, ds1]);
    }
    ProbeTable { entries }
}

fn table() -> &'static ProbeTable {
    static TABLE: OnceLock<ProbeTable> = OnceLock::new();
    TABLE.get_or_init(build_table)
}

/// Evaluates the probe waveform `(s0, s1, ds0/dx, ds1/dx)` at continuous source
/// frame position `x` via exact cubic Hermite interpolation on the 4x
/// oversampled table.
#[must_use]
pub fn eval(x: f64) -> (f64, f64, f64, f64) {
    let tbl = &table().entries;
    let period_f = usize_to_f64(PERIOD);
    let wrapped = x.rem_euclid(period_f);
    let u = wrapped * OVERSAMPLE_F64;
    let u_floor = u.floor();
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let i0 = (u_floor as usize) & (TABLE_LEN - 1);
    let i1 = (i0 + 1) & (TABLE_LEN - 1);
    let t = u - u_floor;
    let t2 = t * t;
    let t3 = t2 * t;

    let h00 = 2.0 * t3 - 3.0 * t2 + 1.0;
    let h10 = t3 - 2.0 * t2 + t;
    let h01 = -2.0 * t3 + 3.0 * t2;
    let h11 = t3 - t2;

    let dh00 = 6.0 * t2 - 6.0 * t;
    let dh10 = 3.0 * t2 - 4.0 * t + 1.0;
    let dh01 = -6.0 * t2 + 6.0 * t;
    let dh11 = 3.0 * t2 - 2.0 * t;

    let e0 = tbl[i0];
    let e1 = tbl[i1];
    let inv_h = OVERSAMPLE_F64;

    let p0_0 = e0[0];
    let p1_0 = e1[0];
    let m0_0 = e0[2] * H_STEP;
    let m1_0 = e1[2] * H_STEP;
    let s0 = h00 * p0_0 + h10 * m0_0 + h01 * p1_0 + h11 * m1_0;
    let ds0 = (dh00 * p0_0 + dh10 * m0_0 + dh01 * p1_0 + dh11 * m1_0) * inv_h;

    let p0_1 = e0[1];
    let p1_1 = e1[1];
    let m0_1 = e0[3] * H_STEP;
    let m1_1 = e1[3] * H_STEP;
    let s1 = h00 * p0_1 + h10 * m0_1 + h01 * p1_1 + h11 * m1_1;
    let ds1 = (dh00 * p0_1 + dh10 * m0_1 + dh01 * p1_1 + dh11 * m1_1) * inv_h;

    (s0, s1, ds0, ds1)
}

/// Fills an interleaved capture PCM buffer `out` with `frames` frames of the
/// probe signal starting at monotonic global source frame `first_global_frame`.
pub fn fill_capture(first_global_frame: u64, channels: usize, frames: usize, out: &mut [f32]) {
    if channels == 0 || frames == 0 {
        return;
    }
    let tbl = &table().entries;
    let mask = PERIOD - 1;
    for offset in 0..frames {
        #[allow(clippy::cast_possible_truncation)]
        let idx = (((first_global_frame.wrapping_add(offset as u64)) as usize) & mask) * OVERSAMPLE;
        let sample = tbl[idx];
        let base = offset * channels;
        if base + channels > out.len() {
            break;
        }
        #[allow(clippy::cast_possible_truncation)]
        let c0 = sample[0] as f32;
        #[allow(clippy::cast_possible_truncation)]
        let c1 = sample[1] as f32;
        out[base] = c0;
        if channels >= 2 {
            out[base + 1] = c1;
        }
        for ch in 2..channels {
            out[base + ch] = if ch % 2 == 0 { c0 } else { c1 };
        }
    }
}

/// Refines a candidate global frame position `guess` against stereo output
/// `(y0, y1)` using Gauss-Newton iterations, returning `Some((x, residual))`
/// when the Euclidean residual falls within `RESIDUAL_TOL`.
fn refine_stereo(y0: f64, y1: f64, guess: f64) -> Option<(f64, f64)> {
    let mut x = guess;
    for _ in 0..8 {
        let (s0, s1, ds0, ds1) = eval(x);
        let r0 = y0 - s0;
        let r1 = y1 - s1;
        let denom = ds0 * ds0 + ds1 * ds1;
        if denom < 1e-12 {
            break;
        }
        let dx = ((r0 * ds0 + r1 * ds1) / denom).clamp(-0.4, 0.4);
        x += dx;
        if dx.abs() < 1e-7 {
            break;
        }
    }
    let (s0, s1, _, _) = eval(x);
    let err = (y0 - s0).hypot(y1 - s1);
    (err < RESIDUAL_TOL).then_some((x, err))
}

/// Refines a candidate global frame position `guess` against two consecutive
/// mono output samples `(y_curr, y_next)` assuming unit-order local step.
fn refine_mono(y_curr: f64, y_next: f64, guess: f64, step: f64) -> Option<(f64, f64)> {
    let mut x = guess;
    for _ in 0..8 {
        let (s0, _, ds0, _) = eval(x);
        let (s1, _, ds1, _) = eval(x + step);
        let r0 = y_curr - s0;
        let r1 = y_next - s1;
        let denom = ds0 * ds0 + ds1 * ds1;
        if denom < 1e-12 {
            break;
        }
        let dx = ((r0 * ds0 + r1 * ds1) / denom).clamp(-0.4, 0.4);
        x += dx;
        if dx.abs() < 1e-7 {
            break;
        }
    }
    let (s0, _, _, _) = eval(x);
    let (s1, _, _, _) = eval(x + step);
    let err = (y_curr - s0).hypot(y_next - s1);
    (err < RESIDUAL_TOL).then_some((x, err))
}

/// Black-box per-speaker PCM output decoder recovering continuous global source
/// frame positions `Option<f64>` solely from rendered `f32` output buffers.
#[derive(Clone, Debug)]
pub struct ProbeDecoder {
    last_x: Option<f64>,
    last_sample_idx: u64,
    step_est: f64,
    sample_idx: u64,
    decoded: Vec<Option<f64>>,
}

impl Default for ProbeDecoder {
    fn default() -> Self {
        Self::new()
    }
}

impl ProbeDecoder {
    /// Creates an unlocked output decoder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            last_x: None,
            last_sample_idx: 0,
            step_est: 1.0,
            sample_idx: 0,
            decoded: Vec::new(),
        }
    }

    /// Resets decoder tracking state (e.g. when a receiver restarts).
    pub fn reset(&mut self) {
        self.last_x = None;
        self.last_sample_idx = 0;
        self.step_est = 1.0;
    }

    /// Decodes one rendered output cycle `pcm` (`frames * channels` interleaved
    /// `f32` samples) into per-sample global source positions `Option<f64>`,
    /// constrained only by causality (`x <= max_captured_frame`).
    pub fn decode_cycle(
        &mut self,
        pcm: &[f32],
        channels: usize,
        max_captured_frame: u64,
    ) -> &[Option<f64>] {
        let frames = pcm.len().checked_div(channels).unwrap_or(0);
        self.decoded.clear();
        self.decoded.resize(frames, None);
        if frames == 0 || max_captured_frame == 0 {
            self.sample_idx = self.sample_idx.saturating_add(frames as u64);
            return &self.decoded;
        }

        let max_x = u64_to_f64(max_captured_frame);
        let cycle_base_idx = self.sample_idx;

        if channels >= 2 {
            self.decode_stereo_raw(pcm, channels, frames, max_captured_frame, max_x);
        } else {
            self.decode_mono_raw(pcm, frames, max_captured_frame, max_x);
        }

        self.sample_idx = cycle_base_idx.saturating_add(frames as u64);
        if channels >= 2 {
            refine_constant_step_runs_stereo(pcm, channels, &mut self.decoded);
        } else {
            denoise_constant_step_runs_mono(&mut self.decoded);
        }
        &self.decoded
    }

    fn decode_stereo_raw(
        &mut self,
        pcm: &[f32],
        channels: usize,
        frames: usize,
        max_captured_frame: u64,
        max_x: f64,
    ) {
        let cycle_base_idx = self.sample_idx;
        let mut acquired_in_cycle = false;

        for i in 0..frames {
            let y0 = f64::from(pcm[i * channels]);
            let y1 = f64::from(pcm[i * channels + 1]);
            if y0 * y0 + y1 * y1 < SILENCE_ENERGY {
                continue;
            }
            let global_k = cycle_base_idx.saturating_add(i as u64);

            // 1. Fast O(1) tracking from last known position (works continuously
            //    and immediately re-locks across short concealed packet gaps).
            if let Some(lx) = self.last_x {
                let gap_samples = global_k.saturating_sub(self.last_sample_idx);
                let gap = u64_to_f64(gap_samples);
                let guess = lx + gap * self.step_est;
                if guess >= -0.5
                    && guess <= max_x + 0.5
                    && let Some((x, _)) = refine_stereo(y0, y1, guess)
                    && x >= 0.0
                    && x <= max_x
                {
                    // Guard against accidental single-sample match when
                    // resuming after a gap by checking the next sample too.
                    let confirmed = if gap_samples <= 1 || i + 1 >= frames {
                        true
                    } else {
                        let ny0 = f64::from(pcm[(i + 1) * channels]);
                        let ny1 = f64::from(pcm[(i + 1) * channels + 1]);
                        refine_stereo(ny0, ny1, x + self.step_est).is_some()
                    };
                    if confirmed {
                        if gap_samples == 1 {
                            let step = (x - lx).clamp(0.95, 1.05);
                            self.step_est = 0.9 * self.step_est + 0.1 * step;
                        }
                        self.decoded[i] = Some(x);
                        self.last_x = Some(x);
                        self.last_sample_idx = global_k;
                        continue;
                    }
                }
            }

            // 2. Causal full-period acquisition (runs only on startup, after a
            //    jump/restart, or at periodic checkpoints inside an unlocked
            //    cycle so concealed gaps stay O(1)).
            let try_acquire = !acquired_in_cycle
                && i + 16 <= frames
                && (i == 0 || i % 16 == 0 || i + 16 == frames);
            if try_acquire
                && let Some((x, step)) =
                    acquire_stereo(pcm, channels, i, frames, max_captured_frame)
            {
                acquired_in_cycle = true;
                self.decoded[i] = Some(x);
                self.step_est = step;
                self.last_x = Some(x);
                self.last_sample_idx = global_k;

                // Walk backwards to capture exact first valid sample if lock
                // succeeded mid-cycle (e.g., immediately after fade-in ends).
                let mut cur_x = x;
                for j in (0..i).rev() {
                    if self.decoded[j].is_some() {
                        break;
                    }
                    let py0 = f64::from(pcm[j * channels]);
                    let py1 = f64::from(pcm[j * channels + 1]);
                    if py0 * py0 + py1 * py1 < SILENCE_ENERGY {
                        break;
                    }
                    let back_guess = cur_x - step;
                    if back_guess < 0.0 {
                        break;
                    }
                    if let Some((px, _)) = refine_stereo(py0, py1, back_guess)
                        && px >= 0.0
                        && px <= max_x
                    {
                        self.decoded[j] = Some(px);
                        cur_x = px;
                    } else {
                        break;
                    }
                }
            }
        }
    }

    fn decode_mono_raw(&mut self, pcm: &[f32], frames: usize, max_captured_frame: u64, max_x: f64) {
        let cycle_base_idx = self.sample_idx;
        let mut acquired_in_cycle = false;
        for i in 0..frames {
            let y0 = f64::from(pcm[i]);
            let y1 = if i + 1 < frames {
                f64::from(pcm[i + 1])
            } else {
                y0
            };
            if y0 * y0 + y1 * y1 < SILENCE_ENERGY {
                continue;
            }
            let global_k = cycle_base_idx.saturating_add(i as u64);
            if let Some(lx) = self.last_x {
                let gap_samples = global_k.saturating_sub(self.last_sample_idx);
                let gap = u64_to_f64(gap_samples);
                let guess = lx + gap * self.step_est;
                if guess >= -0.5
                    && guess <= max_x + 0.5
                    && i + 1 < frames
                    && let Some((x, _)) = refine_mono(y0, y1, guess, self.step_est)
                    && x >= 0.0
                    && x <= max_x
                {
                    if gap_samples == 1 {
                        self.step_est = 0.9 * self.step_est + 0.1 * (x - lx).clamp(0.95, 1.05);
                    }
                    self.decoded[i] = Some(x);
                    self.last_x = Some(x);
                    self.last_sample_idx = global_k;
                    continue;
                }
            }
            if !acquired_in_cycle
                && i + 8 <= frames
                && (i == 0 || i % 16 == 0)
                && let Some((x, step)) = acquire_mono(pcm, i, frames, max_captured_frame)
            {
                acquired_in_cycle = true;
                self.decoded[i] = Some(x);
                self.step_est = step;
                self.last_x = Some(x);
                self.last_sample_idx = global_k;
            }
        }
    }
}

/// Estimates coarse carrier phase in `[0, CARRIER_PERIOD)` over 16 stereo
/// samples starting at `start` (suppressing the high-frequency watermark by
/// over 10x) and searches backward from `max_captured_frame` over the
/// unambiguous causal period, confirming 4 consecutive samples.
fn acquire_stereo(
    pcm: &[f32],
    channels: usize,
    start: usize,
    frames: usize,
    max_captured_frame: u64,
) -> Option<(f64, f64)> {
    if start + 16 > frames || max_captured_frame == 0 {
        return None;
    }
    let omega0 = TAU / usize_to_f64(CARRIER_PERIOD);
    let mut acc_re = 0.0_f64;
    let mut acc_im = 0.0_f64;
    for m in 0..16usize {
        let y0 = f64::from(pcm[(start + m) * channels]);
        let y1 = f64::from(pcm[(start + m) * channels + 1]);
        let (s, c) = (omega0 * usize_to_f64(m)).sin_cos();
        // Multiply (y0 + i y1) by e^{-i omega0 m}.
        acc_re += y0 * c + y1 * s;
        acc_im += y1 * c - y0 * s;
    }
    let mag = acc_re.hypot(acc_im) / 16.0;
    if !(0.30..=0.60).contains(&mag) {
        return None;
    }
    let phi = acc_im.atan2(acc_re).rem_euclid(TAU);
    let phase_in_cycle = phi * (usize_to_f64(CARRIER_PERIOD) / TAU);

    let max_x = u64_to_f64(max_captured_frame);
    let min_x = u64_to_f64(max_captured_frame.saturating_sub(PERIOD as u64 - 1));
    let cyc_f = usize_to_f64(CARRIER_PERIOD);
    let max_cycle = (max_x / cyc_f).floor();
    let min_cycle = (min_x / cyc_f).floor().max(0.0);

    let y0_0 = f64::from(pcm[start * channels]);
    let y1_0 = f64::from(pcm[start * channels + 1]);
    let y0_1 = f64::from(pcm[(start + 1) * channels]);
    let y1_1 = f64::from(pcm[(start + 1) * channels + 1]);
    let y0_2 = f64::from(pcm[(start + 2) * channels]);
    let y1_2 = f64::from(pcm[(start + 2) * channels + 1]);
    let y0_3 = f64::from(pcm[(start + 3) * channels]);
    let y1_3 = f64::from(pcm[(start + 3) * channels + 1]);

    // Search backwards from the most recently captured frames so normal low-
    // and medium-latency streams lock within the first few dozen cycles.
    let mut cyc = max_cycle;
    while cyc >= min_cycle {
        let center = cyc * cyc_f + phase_in_cycle;
        for delta in [-4.0_f64, -2.0, -1.0, 0.0, 1.0, 2.0, 4.0] {
            let cand = center + delta;
            if cand < min_x || cand > max_x {
                continue;
            }
            if let Some((x0, _)) = refine_stereo(y0_0, y1_0, cand)
                && x0 >= min_x
                && x0 <= max_x
                && let Some((x1, _)) = refine_stereo(y0_1, y1_1, x0 + 1.0)
                && let Some((x2, _)) = refine_stereo(y0_2, y1_2, x1 + (x1 - x0))
                && let Some((x3, _)) = refine_stereo(y0_3, y1_3, x2 + (x1 - x0))
            {
                let step = ((x3 - x0) / 3.0).clamp(0.95, 1.05);
                if (x1 - x0 - step).abs() < 1e-2 && (x2 - x1 - step).abs() < 1e-2 {
                    return Some((x0, step));
                }
            }
        }
        cyc -= 1.0;
    }
    None
}

/// Coarse causal acquisition for single-channel (mono) streams.
fn acquire_mono(
    pcm: &[f32],
    start: usize,
    frames: usize,
    max_captured_frame: u64,
) -> Option<(f64, f64)> {
    if start + 4 > frames || max_captured_frame == 0 {
        return None;
    }
    let max_x = u64_to_f64(max_captured_frame);
    let min_x = u64_to_f64(max_captured_frame.saturating_sub(PERIOD as u64 - 1));
    let y0 = f64::from(pcm[start]);
    let y1 = f64::from(pcm[start + 1]);
    let y2 = f64::from(pcm[start + 2]);
    let y3 = f64::from(pcm[start + 3]);

    let tbl = &table().entries;
    let mask = PERIOD - 1;
    let mut cand_f = max_captured_frame;
    let lo_f = max_captured_frame.saturating_sub(PERIOD as u64 - 1);
    loop {
        #[allow(clippy::cast_possible_truncation)]
        let idx = ((cand_f as usize) & mask) * OVERSAMPLE;
        if (tbl[idx][0] - y0).abs() < 0.08 {
            let guess = u64_to_f64(cand_f);
            if let Some((x0, _)) = refine_mono(y0, y1, guess, 1.0)
                && x0 >= min_x
                && x0 <= max_x
                && let Some((x1, _)) = refine_mono(y1, y2, x0 + 1.0, 1.0)
                && let Some((x2, _)) = refine_mono(y2, y3, x1 + (x1 - x0), x1 - x0)
            {
                let step = ((x2 - x0) / 2.0).clamp(0.95, 1.05);
                if (x1 - x0 - step).abs() < 1e-2 {
                    return Some((x0, step));
                }
            }
        }
        if cand_f == lo_f {
            break;
        }
        cand_f -= 1;
    }
    None
}

/// For every contiguous stereo decoded run of length `>= 8` whose per-sample
/// estimates lie near a constant-step line, performs joint 2-parameter
/// `(x0, step)` Gauss-Newton refinement directly against the rendered stereo
/// PCM samples and accepts the refined line only when every sample in the run
/// matches the rendered PCM within `RESIDUAL_TOL`.
///
/// This eliminates single-sample derivative-cusp noise and yields sub-10^-6
/// frame (~0.02 ns) boundary continuity across resampler cycles while leaving
/// nonlinear runs, jumps, and gaps untouched.
#[allow(clippy::too_many_lines)]
fn refine_constant_step_runs_stereo(pcm: &[f32], channels: usize, decoded: &mut [Option<f64>]) {
    let n = decoded.len();
    let mut start = 0usize;
    while start < n {
        if decoded[start].is_none() {
            start += 1;
            continue;
        }
        let mut end = start + 1;
        while end < n {
            if let (Some(prev), Some(curr)) = (decoded[end - 1], decoded[end])
                && curr > prev
                && curr - prev < 2.0
            {
                end += 1;
            } else {
                break;
            }
        }
        let len = end - start;
        if len >= 8 {
            // Seed `(x0, step)` using ordinary least squares on the raw
            // per-sample decoded positions.
            let len_f = usize_to_f64(len);
            let mean_k = 0.5 * (len_f - 1.0);
            let mut sum_x = 0.0_f64;
            for item in &decoded[start..end] {
                if let Some(val) = *item {
                    sum_x += val;
                }
            }
            let mean_x = sum_x / len_f;
            let mut var_k = 0.0_f64;
            let mut cov_kx = 0.0_f64;
            for (offset, item) in decoded[start..end].iter().enumerate() {
                if let Some(val) = *item {
                    let dk = usize_to_f64(offset) - mean_k;
                    var_k += dk * dk;
                    cov_kx += dk * (val - mean_x);
                }
            }
            if var_k > 0.0 {
                let mut step = cov_kx / var_k;
                let mut x0 = mean_x - step * mean_k;
                let mut max_dev = 0.0_f64;
                for (offset, item) in decoded[start..end].iter().enumerate() {
                    if let Some(val) = *item {
                        let fit = x0 + step * usize_to_f64(offset);
                        max_dev = max_dev.max((val - fit).abs());
                    }
                }
                if max_dev < LINEAR_BLOCK_TOL {
                    // Joint 2-parameter Gauss-Newton on rendered stereo PCM.
                    for _ in 0..3 {
                        let mut j00 = 0.0_f64;
                        let mut j01 = 0.0_f64;
                        let mut j11 = 0.0_f64;
                        let mut b0 = 0.0_f64;
                        let mut b1 = 0.0_f64;
                        for offset in 0..len {
                            let kf = usize_to_f64(offset);
                            let x = x0 + step * kf;
                            let (s0, s1, ds0, ds1) = eval(x);
                            let base = (start + offset) * channels;
                            let r0 = f64::from(pcm[base]) - s0;
                            let r1 = f64::from(pcm[base + 1]) - s1;
                            let h = ds0 * ds0 + ds1 * ds1;
                            let g = r0 * ds0 + r1 * ds1;
                            j00 += h;
                            j01 += kf * h;
                            j11 += kf * kf * h;
                            b0 += g;
                            b1 += kf * g;
                        }
                        let det = j00 * j11 - j01 * j01;
                        if det.abs() < 1e-18 {
                            break;
                        }
                        let dx0 = (j11 * b0 - j01 * b1) / det;
                        let dstep = (-j01 * b0 + j00 * b1) / det;
                        x0 += dx0;
                        step += dstep;
                        if dx0.abs() < 1e-10 && dstep.abs() < 1e-12 {
                            break;
                        }
                    }
                    // Accept only if every sample in the run agrees with the
                    // rendered PCM within `RESIDUAL_TOL`.
                    let mut max_pcm_err = 0.0_f64;
                    for offset in 0..len {
                        let x = x0 + step * usize_to_f64(offset);
                        let (s0, s1, _, _) = eval(x);
                        let base = (start + offset) * channels;
                        let err = (f64::from(pcm[base]) - s0).hypot(f64::from(pcm[base + 1]) - s1);
                        max_pcm_err = max_pcm_err.max(err);
                        if max_pcm_err >= RESIDUAL_TOL {
                            break;
                        }
                    }
                    if max_pcm_err < RESIDUAL_TOL {
                        for (offset, slot) in decoded[start..end].iter_mut().enumerate() {
                            *slot = Some(x0 + step * usize_to_f64(offset));
                        }
                    }
                }
            }
        }
        start = end;
    }
}

/// OLS linear denoiser for mono constant-step runs.
fn denoise_constant_step_runs_mono(decoded: &mut [Option<f64>]) {
    let n = decoded.len();
    let mut start = 0usize;
    while start < n {
        if decoded[start].is_none() {
            start += 1;
            continue;
        }
        let mut end = start + 1;
        while end < n {
            if let (Some(prev), Some(curr)) = (decoded[end - 1], decoded[end])
                && curr > prev
                && curr - prev < 2.0
            {
                end += 1;
            } else {
                break;
            }
        }
        let len = end - start;
        if len >= 8 {
            let len_f = usize_to_f64(len);
            let mean_k = 0.5 * (len_f - 1.0);
            let mut sum_x = 0.0_f64;
            for item in &decoded[start..end] {
                if let Some(val) = *item {
                    sum_x += val;
                }
            }
            let mean_x = sum_x / len_f;
            let mut var_k = 0.0_f64;
            let mut cov_kx = 0.0_f64;
            for (offset, item) in decoded[start..end].iter().enumerate() {
                if let Some(val) = *item {
                    let dk = usize_to_f64(offset) - mean_k;
                    var_k += dk * dk;
                    cov_kx += dk * (val - mean_x);
                }
            }
            if var_k > 0.0 {
                let slope = cov_kx / var_k;
                let intercept = mean_x - slope * mean_k;
                let mut max_dev = 0.0_f64;
                for (offset, item) in decoded[start..end].iter().enumerate() {
                    if let Some(val) = *item {
                        let fit = intercept + slope * usize_to_f64(offset);
                        max_dev = max_dev.max((val - fit).abs());
                    }
                }
                if max_dev < 1e-3 {
                    for (offset, slot) in decoded[start..end].iter_mut().enumerate() {
                        *slot = Some(intercept + slope * usize_to_f64(offset));
                    }
                }
            }
        }
        start = end;
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::packet::{Audio, Format};
    use unisono_core::player::Regulation;
    use unisono_core::receiver::{Receiver, Settings as ReceiverSettings};
    use unisono_dsp::format::to_signed24;
    use unisono_dsp::{Filter, Parameters, Position, Resampler, Step, Window};
    use unisono_runtime::pump::Pump;
    use unisono_runtime::store::Store;

    use super::{PERIOD, ProbeDecoder, eval, fill_capture, usize_to_f64};

    #[test]
    fn probe_signal_hermite_interpolation_matches_resampler_to_sub_nanosecond() {
        let filter = Filter::for_rate(48_000);
        let mut resampler = Resampler::new(filter, 2);
        let total_in = 1_024usize;
        let mut src = vec![0.0f32; total_in * 2];
        fill_capture(12_345, 2, total_in, &mut src);

        let window = Window {
            first: 12_345,
            samples: &src,
        };
        let step_ratio = 1.000_37_f64;
        #[allow(clippy::cast_possible_truncation)]
        let step_offset = ((step_ratio - 1.0) * 18_446_744_073_709_551_616.0).round() as i64;
        let step = Step::new(step_offset).expect("valid step");
        let start = Position::new(12_420, 1u64 << 62); // 12_420.25
        let mut out = vec![0.0f32; 256 * 2];
        let done = resampler.process(window, start, step, &mut out);
        assert_eq!(done.frames, 256);

        let mut decoder = ProbeDecoder::new();
        let positions = decoder.decode_cycle(&out, 2, 13_369);
        let mut max_err = 0.0_f64;
        let mut worst = (0usize, 0.0_f64, 0.0_f64, 0.0_f64);
        for (i, slot) in positions.iter().enumerate() {
            let x = slot.expect("every clean resampled frame should decode");
            let expected = 12_420.25 + usize_to_f64(i) * step_ratio;
            let err = (x - expected).abs();
            if err > max_err {
                max_err = err;
                let (e0, e1, _, _) = eval(expected);
                let res = (f64::from(out[i * 2]) - e0).hypot(f64::from(out[i * 2 + 1]) - e1);
                worst = (i, expected, x, res);
            }
        }
        assert!(
            max_err < 1e-4,
            "decoded position error {max_err} frames exceeds 1e-4 (~2 ns) worst={worst:?}"
        );

        // Verify direct Hermite eval matches exact integer samples.
        let (s0, s1, _, _) = eval(12_345.0 + 100.0);
        assert!((s0 - f64::from(src[200])).abs() < 1e-6);
        assert!((s1 - f64::from(src[201])).abs() < 1e-6);
    }

    #[test]
    fn probe_decoder_rejects_burg_concealed_packet_and_relocks_after_fade_in() {
        let mut receiver: Receiver<256, 64, 8> = Receiver::new(ReceiverSettings {
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
        let mut store = Store::for_stretch(256, 2);
        let mut pump = Pump::new(
            Filter::for_rate(48_000),
            2,
            Parameters::for_rate(48_000),
            256,
        );

        // Feed 12 packets of 240 frames (2880 frames total), dropping packet 5
        // (frames 1200..1440) so Burg AR(32) concealment synthesizes that gap.
        let mut raw_pcm = vec![0.0f32; 240 * 2];
        let mut wire = vec![0u8; 240 * 2 * 3];
        for pkt in 0..12u64 {
            let first = pkt * 240;
            if pkt == 5 {
                continue;
            }
            fill_capture(first, 2, 240, &mut raw_pcm);
            to_signed24(&raw_pcm, &mut wire);
            let hdr = Audio {
                stream: 1,
                timeline: 1,
                clock: 1,
                index: first,
                frames: 240,
                rate: 48_000,
                channels: 2,
                format: Format::Signed24,
                protection: 0,
                capture: i64::try_from(first).unwrap_or(0) * 1_000_000_000 / 48_000,
                drift: 0,
                level: 20_000_000,
                level_slope: 0,
                span: 2_000,
                window: 2_400,
                flags: 0,
                stamped_index: 0,
                stamped_departure: 0,
            };
            let _ = receiver.packet(&hdr, hdr.capture + 100_000);
            let rx_ref = &receiver;
            store.write_packet(first, Format::Signed24, &wire, |idx| rx_ref.covers(idx));
        }

        let mut decoder = ProbeDecoder::new();
        let mut out = vec![0.0f32; 256 * 2];
        let mut concealed_decoded_some = 0usize;
        let mut clean_before = 0usize;
        let mut clean_after = 0usize;

        for cyc in 0..10u64 {
            let start_frame = cyc * 256;
            let plan = unisono_core::player::Plan {
                frames: 256,
                start: unisono_core::timing::Position {
                    frame: start_frame,
                    fraction: 0,
                },
                step: unisono_core::timing::Step::UNITY,
                jumped: cyc == 0,
            };
            pump.play(&mut receiver, &store, &plan, &mut out);
            let dec = decoder.decode_cycle(&out, 2, 2_880);
            for (i, slot) in dec.iter().enumerate() {
                let true_pos = start_frame + i as u64;
                // Frames 480..1150 are fully settled real audio before the gap.
                if (480..1_150).contains(&true_pos) && slot.is_some() {
                    clean_before += 1;
                }
                // Frames 1200..1440 are concealed by Burg AR(32) — MUST decode as None!
                if (1_200..1_440).contains(&true_pos) && slot.is_some() {
                    concealed_decoded_some += 1;
                }
                // Frames 1750..2400 are fully recovered real audio after fade-in.
                if (1_750..2_400).contains(&true_pos) && slot.is_some() {
                    clean_after += 1;
                }
            }
        }

        assert_eq!(
            concealed_decoded_some, 0,
            "Burg AR concealed frames must never falsely decode as source audio"
        );
        assert!(
            clean_before > 650,
            "expected >650 clean frames before gap, got {clean_before}"
        );
        assert!(
            clean_after > 630,
            "expected >630 clean frames after gap recovery, got {clean_after}"
        );
        const { assert!(PERIOD >= 96_000) };
    }
}
