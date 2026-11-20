// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fades, and the concealment of gaps in a stream.
//!
//! When frames are missing, what is played in their place continues the
//! sound that came before and fades it out, and when frames arrive again
//! they are faded in. Nothing is delayed for this: the continuation is made
//! from the frames already played.
//!
//! `docs/concealment.md` states what a concealment computes as a problem of
//! inference, which instance of it this module solves, and how the
//! alternatives compare.
//!
//! # The continuation
//!
//! The continuation is a linear prediction. Each channel's last frames
//! before the gap are fitted with a model in which a sample is a weighted
//! sum of the `order` samples before it. The weights are found by Burg's
//! method, which minimizes the error of predicting each fitted sample from
//! those before it and from those after it. The model then predicts the
//! missing samples one after another, each from the predictions before it.
//!
//! The continuation starts where the sound left off, so a gap begins
//! without a step. It cannot grow: Burg's method only gives models whose
//! free response does not grow, and what is played is also kept within the
//! largest sample of the fitted frames. This is why the method was chosen.
//! A fit by least squares over the same frames was tried: it continues a
//! single tone exactly, but for a sound of many close partials it gave
//! models that grow.
//!
//! Its accuracy is modest. With the sizes of [`Parameters::for_rate`] at
//! 48 000 frames per second, a single steady tone of 50 Hz or more is
//! continued within 2 % of its amplitude over the first millisecond and
//! within 10 % over the first two; these are the largest errors over some
//! 500 frequencies up to 20 kHz and 16 phases, and the tests assert 3 % and
//! 15 %. After 5 ms the error can be half the amplitude. A sound of several
//! close partials, or a tone so low that the fitted frames hold less than a
//! cycle of it, is followed for a shorter time, and its continuation then
//! dies away by itself. Noise cannot be predicted, and its continuation
//! dies away within a few frames. The continuation therefore covers the
//! start of a gap, where it resembles the sound, and the fade out removes
//! it before it has lasted long.
//!
//! # The fades
//!
//! A fade is a raised cosine. The continuation starts at full level and
//! reaches silence `fade_out` frames into the gap. When frames arrive again
//! they are mixed with the continuation, which keeps running: the arriving
//! frames rise by a raised cosine over `fade_in` frames while what is left
//! of the continuation falls, the two weights adding up to one.
//!
//! A gap that begins before the fade in is complete does not get a whole
//! new fade out. The sound just played was then partly a continuation
//! itself, and continuing it at full level again and again would keep a
//! sound alive that the stream never held. Such a gap enters the fade out
//! part-way: at the place the last continuation had reached, times the
//! share of the fade in that was still missing.

use std::f64::consts::PI;

/// A raised-cosine fade over a number of frames.
#[derive(Clone, Debug)]
pub struct Fade {
    rising: Box<[f32]>,
}

impl Fade {
    /// A fade that takes `frames` frames.
    #[must_use]
    pub fn new(frames: usize) -> Fade {
        #![allow(clippy::cast_precision_loss)] // lengths of fades are small
        let quarter_turns = 2.0 * (frames as f64 + 1.0);
        let rising = (0..frames)
            .map(|frame| {
                let sine = (PI * (frame as f64 + 1.0) / quarter_turns).sin();
                #[allow(clippy::cast_possible_truncation)] // rounding to f32 is intended
                let gain = (sine * sine) as f32;
                gain
            })
            .collect();
        Fade { rising }
    }

    /// The number of frames the fade takes.
    #[must_use]
    pub fn frames(&self) -> usize {
        self.rising.len()
    }

    /// The gain of frame `frame` of a fade in:
    /// `sin^2(pi (frame + 1) / (2 (frames + 1)))`, which is above zero and
    /// below one, and one from frame `frames` on.
    #[must_use]
    pub fn rising(&self, frame: usize) -> f32 {
        self.rising.get(frame).copied().unwrap_or(1.0)
    }

    /// The gain of frame `frame` of a fade out:
    /// `cos^2(pi (frame + 1) / (2 (frames + 1)))`, which is below one and
    /// above zero, and zero from frame `frames` on. It is what
    /// [`Fade::rising`] lacks to one.
    #[must_use]
    pub fn falling(&self, frame: usize) -> f32 {
        self.rising
            .len()
            .checked_sub(frame)
            .and_then(|left| left.checked_sub(1))
            .and_then(|mirrored| self.rising.get(mirrored))
            .copied()
            .unwrap_or(0.0)
    }
}

/// The sizes that decide how a gap is concealed, all in frames.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Parameters {
    /// How many frames before a gap the continuation is fitted to.
    pub fitted: usize,
    /// How many samples predict the next one.
    pub order: usize,
    /// How long the continuation takes to fade out.
    pub fade_out: usize,
    /// How long arriving frames take to fade in.
    pub fade_in: usize,
}

impl Parameters {
    /// The largest number of fitted frames.
    pub const LARGEST_FITTED: usize = 1 << 14;
    /// The largest order.
    pub const LARGEST_ORDER: usize = 256;
    /// The largest length of a fade.
    pub const LARGEST_FADE: usize = 1 << 20;

    /// Sizes for a stream of `rate` frames per second: the continuation is
    /// fitted to 10 ms with order 32 and fades out over 20 ms, and arriving
    /// frames fade in over 5 ms.
    ///
    /// Sound is roughly steady over some tens of milliseconds, which bounds
    /// both how much of the past says something about the gap and how far
    /// into the gap a continuation is worth playing. The fade in is long
    /// enough to spread its own spectrum over no more than a few hundred
    /// hertz.
    #[must_use]
    pub fn for_rate(rate: u32) -> Parameters {
        let frames = |milliseconds: u64| {
            usize::try_from(u64::from(rate) * milliseconds / 1000).unwrap_or(usize::MAX)
        };
        Parameters {
            fitted: frames(10),
            order: 32,
            fade_out: frames(20),
            fade_in: frames(5),
        }
        .within_limits()
    }

    /// The same sizes, each brought within its limit, and the order to at
    /// most half the number of fitted frames.
    #[must_use]
    pub fn within_limits(self) -> Parameters {
        let fitted = self.fitted.min(Parameters::LARGEST_FITTED);
        Parameters {
            fitted,
            order: self.order.min(Parameters::LARGEST_ORDER).min(fitted / 2),
            fade_out: self.fade_out.min(Parameters::LARGEST_FADE),
            fade_in: self.fade_in.min(Parameters::LARGEST_FADE),
        }
    }
}

/// Conceals the gaps of one stream.
///
/// Every frame of the stream passes through it in order, by
/// [`Concealment::pass`] when it has arrived and by [`Concealment::fill`]
/// when it has not. A new one is in the state that a long gap leaves, so the
/// first frames of a stream fade in.
///
/// What it writes depends only on the frames and on which of them were
/// missing, not on how they were grouped into calls. After construction it
/// allocates nothing. At the first missing frame of a gap it fits the
/// continuation, which takes a number of operations proportional to
/// `fitted * order` for each channel: some tens of microseconds a channel
/// on a desktop processor with the sizes of [`Parameters::for_rate`].
#[derive(Clone, Debug)]
pub struct Concealment {
    channels: usize,
    parameters: Parameters,
    fade_out: Fade,
    fade_in: Fade,
    /// The last `fitted` frames that left, as a ring.
    history: Box<[f32]>,
    /// The place in the ring of the oldest frame, which the next one replaces.
    oldest: usize,
    /// For each channel, the weights of the last `order` samples, oldest first.
    weights: Box<[f64]>,
    /// For each channel, the last `order` samples of the continuation, oldest first.
    recent: Box<[f64]>,
    /// For each channel, the largest size of a sample in the fitted frames.
    peak: Box<[f64]>,
    forward: Box<[f64]>,
    backward: Box<[f64]>,
    model: Box<[f64]>,
    shorter: Box<[f64]>,
    /// How far into the fade out the continuation is.
    age: usize,
    /// The gain of the fade out where the continuation entered it.
    entered: f32,
    /// How many frames have faded in since the last gap.
    recovered: usize,
    /// Whether the last frame was missing.
    in_gap: bool,
}

impl Concealment {
    /// A concealment for frames of `channels` samples. The parameters are
    /// brought within their limits.
    #[must_use]
    pub fn new(channels: usize, parameters: Parameters) -> Concealment {
        let parameters = parameters.within_limits();
        let Parameters { fitted, order, .. } = parameters;
        let zeros = |length: usize| vec![0.0f64; length].into_boxed_slice();
        Concealment {
            channels,
            parameters,
            fade_out: Fade::new(parameters.fade_out),
            fade_in: Fade::new(parameters.fade_in),
            history: vec![0.0f32; fitted * channels].into_boxed_slice(),
            oldest: 0,
            weights: zeros(order * channels),
            recent: zeros(order * channels),
            peak: zeros(channels),
            forward: zeros(fitted),
            backward: zeros(fitted),
            model: zeros(order + 1),
            shorter: zeros(order + 1),
            age: parameters.fade_out,
            entered: 0.0,
            recovered: 0,
            in_gap: true,
        }
    }

    /// The sizes in use.
    #[must_use]
    pub fn parameters(&self) -> Parameters {
        self.parameters
    }

    /// The fade that the continuation falls by.
    #[must_use]
    pub fn fade_out(&self) -> &Fade {
        &self.fade_out
    }

    /// The fade that arriving frames rise by.
    #[must_use]
    pub fn fade_in(&self) -> &Fade {
        &self.fade_in
    }

    /// Takes frames that have arrived. They are left as they are, except
    /// for the first `fade_in` frames after a gap, which are faded in and
    /// mixed with what is left of the continuation.
    pub fn pass(&mut self, frames: &mut [f32]) {
        if self.channels == 0 {
            return;
        }
        for frame in frames.chunks_exact_mut(self.channels) {
            self.in_gap = false;
            if self.recovered < self.fade_in.frames() {
                let weight = self.fade_in.rising(self.recovered);
                let gain = self.gain();
                for (channel, sample) in frame.iter_mut().enumerate() {
                    let continued = self.continued(channel, gain);
                    *sample = continued + weight * (*sample - continued);
                }
                self.age = self.age.saturating_add(1).min(self.fade_out.frames());
                self.recovered += 1;
            }
            self.remember(frame);
        }
    }

    /// Writes frames in the place of frames that have not arrived: the
    /// continuation of the sound before, fading out, and then silence.
    pub fn fill(&mut self, frames: &mut [f32]) {
        if self.channels == 0 {
            return;
        }
        if !self.in_gap && frames.len() >= self.channels {
            self.begin_gap();
        }
        for frame in frames.chunks_exact_mut(self.channels) {
            let gain = self.gain();
            for (channel, sample) in frame.iter_mut().enumerate() {
                *sample = self.continued(channel, gain);
            }
            self.age = self.age.saturating_add(1).min(self.fade_out.frames());
            self.remember(frame);
        }
    }

    /// The gain of the continuation at its present age: the fade out from
    /// where the continuation entered it, so that it starts at one.
    fn gain(&self) -> f32 {
        if self.entered > 0.0 {
            (self.fade_out.falling(self.age) / self.entered).min(1.0)
        } else {
            0.0
        }
    }

    /// The next sample of the continuation of `channel`, at `gain`.
    fn continued(&mut self, channel: usize, gain: f32) -> f32 {
        if gain > 0.0 {
            #[allow(clippy::cast_possible_truncation)] // rounding to f32 is intended
            let next = self.predict(channel) as f32;
            next * gain
        } else {
            0.0
        }
    }

    /// Starts a gap: decides where the continuation enters the fade out,
    /// and fits it to the frames that have left.
    fn begin_gap(&mut self) {
        let fade_in = self.fade_in.frames();
        // The share of the fade in that was still missing carries the age of
        // the last continuation over. Both factors are at most 2^20.
        let missing = fade_in.saturating_sub(self.recovered) as u64;
        let carried = (self.age as u64 * missing)
            .checked_div(fade_in as u64)
            .unwrap_or(0);
        self.age = usize::try_from(carried).unwrap_or(usize::MAX);
        self.entered = self.fade_out.falling(self.age);
        self.recovered = 0;
        self.in_gap = true;
        if self.entered > 0.0 {
            self.fit();
        }
    }

    /// Fits each channel's model to the frames that have left, and starts
    /// each continuation from the last of them.
    fn fit(&mut self) {
        let Parameters { fitted, order, .. } = self.parameters;
        for channel in 0..self.channels {
            // The frames in the order they left.
            let ring = self.history.chunks_exact(self.channels);
            let (newer, older) = (ring.clone().take(self.oldest), ring.skip(self.oldest));
            for (value, frame) in self.forward.iter_mut().zip(older.chain(newer)) {
                *value = frame.get(channel).copied().map_or(0.0, f64::from);
            }
            self.backward.copy_from_slice(&self.forward);
            let peak = self
                .forward
                .iter()
                .fold(0.0f64, |peak, x| peak.max(x.abs()));
            let start = channel * order;
            if let (Some(recent), Some(last)) = (
                self.recent.get_mut(start..start + order),
                self.forward.get(fitted - order..),
            ) {
                recent.copy_from_slice(last);
            }
            burg(
                &mut self.forward,
                &mut self.backward,
                &mut self.model,
                &mut self.shorter,
            );
            // The model says x[n] + a[1] x[n-1] + ... + a[order] x[n-order]
            // is small, so the prediction of x[n] weighs x[n-i] by -a[i].
            if let Some(weights) = self.weights.get_mut(start..start + order) {
                for (weight, a) in weights.iter_mut().zip(self.model.iter().skip(1).rev()) {
                    *weight = if a.is_finite() { -a } else { 0.0 };
                }
            }
            if let Some(slot) = self.peak.get_mut(channel) {
                *slot = if peak.is_finite() { peak } else { 0.0 };
            }
        }
    }

    /// The next sample of the continuation of `channel`.
    ///
    /// What is returned is kept within the largest size that a sample had
    /// in the fitted frames, so that whatever the model is, the continuation
    /// is never louder than the sound it continues. The prediction itself
    /// goes on from the value before that limit: a limit inside the
    /// recurrence would disturb it at every crest of the wave, and a model
    /// of a low tone magnifies a small disturbance many times.
    fn predict(&mut self, channel: usize) -> f64 {
        let order = self.parameters.order;
        let start = channel * order;
        let (Some(weights), Some(recent), Some(peak)) = (
            self.weights.get(start..start + order),
            self.recent.get_mut(start..start + order),
            self.peak.get(channel),
        ) else {
            return 0.0;
        };
        let mut next = 0.0;
        for (weight, sample) in weights.iter().zip(recent.iter()) {
            next += weight * sample;
        }
        if !next.is_finite() {
            next = 0.0;
        }
        if order > 0 {
            recent.copy_within(1.., 0);
        }
        if let Some(newest) = recent.last_mut() {
            *newest = next;
        }
        next.clamp(-peak, *peak)
    }

    /// Keeps a frame that has left, in place of the oldest one kept.
    fn remember(&mut self, frame: &[f32]) {
        let start = self.oldest * self.channels;
        if let Some(slot) = self.history.get_mut(start..start + self.channels) {
            slot.copy_from_slice(frame);
            self.oldest += 1;
            if self.oldest == self.parameters.fitted {
                self.oldest = 0;
            }
        }
    }
}

/// Burg's method: fits `model`, the coefficients `a[0] = 1, a[1], ...,
/// a[order]` of a linear prediction, to the samples in `forward`, of which
/// `backward` is a copy. `order` is one less than the length of `model`,
/// and `shorter` is working space of the same length. The samples are
/// overwritten.
///
/// Stage `m` extends the model of order `m` to order `m + 1` by one number,
/// the reflection coefficient, chosen to minimize the summed squares of the
/// errors of predicting each sample from the `m + 1` before it (forward) and
/// from the `m + 1` after it (backward). Its size is at most one, which is
/// what keeps the model's free response from growing. The fitting stops
/// early when the error left is 120 dB below the samples: what is left is
/// rounding, and fitting it would only add noise to the model.
fn burg(forward: &mut [f64], backward: &mut [f64], model: &mut [f64], shorter: &mut [f64]) {
    model.fill(0.0);
    let Some((first, _)) = model.split_first_mut() else {
        return;
    };
    *first = 1.0;
    let order = model.len() - 1;
    let energy: f64 = forward.iter().map(|x| x * x).sum();
    if !(energy > 0.0 && energy.is_finite()) {
        return;
    }
    for stage in 0..order.min(forward.len().saturating_sub(1)) {
        let ahead = forward.iter().skip(stage + 1);
        let behind = backward.iter().skip(stage);
        let (mut product, mut squares) = (0.0, 0.0);
        for (f, b) in ahead.zip(behind) {
            product += f * b;
            squares += f * f + b * b;
        }
        if squares <= 2e-12 * energy {
            break;
        }
        let reflection = (-2.0 * product / squares).clamp(-1.0, 1.0);
        shorter.copy_from_slice(model);
        for index in 1..=stage + 1 {
            model[index] = shorter[index] + reflection * shorter[stage + 1 - index];
        }
        for index in (stage + 1..forward.len()).rev() {
            let (f, b) = (forward[index], backward[index - 1]);
            forward[index] = f + reflection * b;
            backward[index] = b + reflection * f;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::burg;

    /// The first reflection coefficient is minus twice the sum of the
    /// products `x[n] x[n-1]` over the sum of `x[n]^2 + x[n-1]^2`. For
    /// `x[n] = 0.9 x[n-1]` every product is 0.9 times `x[n-1]^2` and every
    /// `x[n]^2` is 0.81 times it, so the coefficient is
    /// `-2 * 0.9 / (1 + 0.81)` whatever the number of samples.
    #[test]
    fn a_geometric_sequence_gives_its_reflection_coefficient() {
        let mut forward: Vec<f64> = (0..50).map(|n| 0.9f64.powi(n)).collect();
        let mut backward = forward.clone();
        let (mut model, mut shorter) = ([0.0; 2], [0.0; 2]);
        burg(&mut forward, &mut backward, &mut model, &mut shorter);
        assert!((model[0] - 1.0).abs() < 1e-15);
        assert!((model[1] + 1.8 / 1.81).abs() < 1e-12, "{}", model[1]);
    }

    /// A sinusoid obeys `x[n] = 2 cos(w) x[n-1] - x[n-2]`. Burg's method
    /// finds that recurrence closely from a few cycles: detects an error in
    /// the update of the model or of the two error sequences from the
    /// second stage on.
    #[test]
    fn a_sinusoid_gives_its_recurrence() {
        let w = 0.3f64;
        let mut forward: Vec<f64> = (0..400).map(|n| (w * f64::from(n) + 0.7).sin()).collect();
        let mut backward = forward.clone();
        let (mut model, mut shorter) = ([0.0; 3], [0.0; 3]);
        burg(&mut forward, &mut backward, &mut model, &mut shorter);
        assert!((model[1] + 2.0 * w.cos()).abs() < 1e-3, "{}", model[1]);
        assert!((model[2] - 1.0).abs() < 1e-3, "{}", model[2]);
    }

    #[test]
    fn silence_and_samples_that_are_not_numbers_give_no_model() {
        for value in [0.0, f64::NAN, f64::INFINITY] {
            let mut forward = [value; 20];
            let mut backward = forward;
            let (mut model, mut shorter) = ([9.0; 5], [0.0; 5]);
            burg(&mut forward, &mut backward, &mut model, &mut shorter);
            assert_eq!(model, [1.0, 0.0, 0.0, 0.0, 0.0]);
        }
        // No coefficients at all, and fewer samples than the order.
        burg(&mut [1.0, 2.0], &mut [1.0, 2.0], &mut [], &mut []);
        let (mut model, mut shorter) = ([0.0; 6], [0.0; 6]);
        burg(&mut [1.0, 2.0], &mut [1.0, 2.0], &mut model, &mut shorter);
        assert!(model.iter().all(|a| a.is_finite()));
    }
}
