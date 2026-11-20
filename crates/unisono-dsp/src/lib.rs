// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Signal processing for unisono: the resampler that corrects clock drift,
//! the sample formats of a packet, and the concealment of gaps.
//!
//! Everything here is a function of its inputs. Nothing allocates after
//! construction, reads a clock or keeps state that the caller cannot see,
//! and the same input gives the same output bit for bit on one platform.
//!
//! # The resampler
//!
//! Two hosts count time with different clocks, so a receiver must play a
//! stream slightly faster or slower than one frame for each frame of its
//! device. [`Resampler`] computes the stream's frames at positions that the
//! caller chooses. A [`Position`] is the index of a frame and a fraction of
//! a frame in units of 2^-64, and a [`Step`], the distance from one output
//! frame to the next, is one frame plus an offset in the same units. They
//! are added as whole numbers, so output frame `i` of a call is taken at
//! exactly `start + i * step`, and positions do not drift however long a
//! stream lasts. One part per billion of rate is about 1.8e10 units.
//!
//! The resampler holds no samples and no position. The caller gives it a
//! [`Window`] of the stream and a starting position at every call, so a
//! jump to another position needs nothing but the next call.
//!
//! ## The filter and its delay
//!
//! The value at a position is a weighted sum of the frames around it, with
//! the weights of the ideal interpolation, `sin(pi t) / (pi t)` at distance
//! `t`, shaped by a Kaiser window ([`Filter`]). The weights are symmetric
//! about the position, so the output is not shifted with respect to the
//! position it was taken at, at any frequency. What the filter costs in
//! time is the frames after the position that it needs: the value at a
//! position can be computed once the frame [`Filter::ahead`] frames after
//! it has arrived, which is half the number of taps, exactly.
//!
//! The error of the interpolation, for a sinusoid of frequency `f`, is made
//! of the sinusoid's images at the sample rate minus `f` and beyond, to the
//! extent the filter lets them through. To keep everything up to 20 kHz
//! the filter must therefore pass 20 kHz and stop the sample rate minus
//! 20 kHz, and the narrower that band is, the longer the filter. The length
//! is computed from the rate and from the error asked for
//! ([`Filter::design`]). For an error 110 dB below a sinusoid:
//!
//! | Frames per second | Taps | Delay in frames | Delay | Error | Ripple to 20 kHz | Stopped from | by |
//! |---|---|---|---|---|---|---|---|
//! | 44 100 | 88 | 44 | 1.00 ms | -114 dB | 0.000 01 dB | 24.1 kHz | 120 dB |
//! | 48 000 | 48 | 24 | 0.50 ms | -111 dB | 0.000 02 dB | 28 kHz | 117 dB |
//! | 88 200 and more | 16 | 8 | 0.09 ms or less | -116 dB or less | | | |
//!
//! The error is the largest difference between the value the filter gives a
//! sinusoid of unit amplitude at or below 20 kHz and the sinusoid's true
//! value, over frequencies and over fractions of a frame. It holds for
//! every step, because each output frame is computed from its position
//! alone. It includes the rounding of the weights to single precision and
//! the linear interpolation between the 1024 tabulated fractions of a
//! frame; with twice as many fractions it would be less than half a decibel
//! smaller. The sum over the taps is taken in double precision and rounded
//! once.
//!
//! A stream that is played at its own rate and on its own frames comes out
//! bit for bit as it went in.
//!
//! # Sample formats
//!
//! [`mod@format`] reads and writes the signed 16-bit and 24-bit samples of a
//! packet. Both fit a single-precision number exactly.
//!
//! # Gaps
//!
//! [`Concealment`] replaces missing frames by a continuation of the sound
//! before them, which fades out, and fades arriving frames in. See
//! [`conceal`] for the method and its limits.

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
