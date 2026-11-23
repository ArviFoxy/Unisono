// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Real-time DSP primitives for `unisono`: arbitrary-rate resampling, PCM
//! sample format conversion, and packet-loss concealment.
//!
//! Deterministic, allocation-free after construction, and free of hidden
//! global state or clock reads.
//!
//! # Resampler
//!
//! [`Resampler`] evaluates the input stream at arbitrary fractional positions
//! to compensate for clock drift. [`Position`] stores a `u64` frame index and
//! `u64` fractional part (`2^-64` frame units), and [`Step`] stores `1 + offset`
//! in the same fixed-point units so `start + i * step` accumulates with zero
//! rounding drift (1 ppb ≈ 1.8e10 units).
//!
//! The resampler is stateless across calls: callers supply a [`Window`] of
//! input frames and a starting [`Position`] each block, making discontinuities
//! trivial.
//!
//! ## Filter Design and Lookahead
//!
//! [`Filter`] tabulates a symmetric Kaiser-windowed sinc kernel (zero group
//! delay distortion) requiring [`Filter::ahead`] (`taps / 2`) lookahead frames.
//! [`Filter::design`] sizes the filter to pass 20 kHz and suppress images
//! above `rate - 20 kHz`. For -110 dB target error (1024-phase table, `f64`
//! accumulation):
//!
//! | Sample rate (Hz) | Taps | Lookahead (frames) | Delay | Worst error | Passband ripple (<= 20 kHz) | Stopband | Attenuation |
//! |---|---|---|---|---|---|---|---|
//! | 44 100 | 88 | 44 | 1.00 ms | -114 dB | 0.000 01 dB | >= 24.1 kHz | 120 dB |
//! | 48 000 | 48 | 24 | 0.50 ms | -111 dB | 0.000 02 dB | >= 28 kHz | 117 dB |
//! | >= 88 200 | 16 | 8 | <= 0.09 ms | <= -116 dB | | | |
//!
//! Unity rate on integer frame positions passes samples through bit-for-bit.
//!
//! # Sample Formats & Concealment
//!
//! - [`mod@format`]: little-endian signed 16-bit and 24-bit PCM conversion.
//! - [`Concealment`] ([`conceal`]): Burg AR gap extrapolation and raised-cosine
//!   crossfades.

#![forbid(unsafe_code)]

pub mod conceal;
pub mod filter;
pub mod format;
pub mod position;
pub mod resample;

pub use conceal::{Concealment, Fade, Parameters};
pub use filter::Filter;
pub use position::{Position, Step};
pub use resample::{Produced, Resampler, Window};
