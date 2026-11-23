// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Floating-point reference estimators used to validate fixed-point
//! implementations in `unisono_core` (test-only).

/// The Kalman filter for an offset whose rate is a random walk.
///
/// The state is the offset `x` between two clocks and its rate `r`. Over a
/// time `dt` the offset grows by `r * dt`, and the rate gains noise of
/// variance `walk * dt`. A measurement is the offset plus noise of variance
/// `noise`. If the two noises are Gaussian with these variances, no estimator
/// has a smaller mean squared error.
#[derive(Clone, Copy, Debug)]
pub struct OffsetKalman {
    walk: f64,
    noise: f64,
    offset: f64,
    rate: f64,
    /// Covariance: variance of the offset, covariance, variance of the rate.
    covariance: [f64; 3],
}

impl OffsetKalman {
    /// A filter that knows nothing yet about an offset near `offset`: its
    /// variance is `offset_variance`, and the rate's is `rate_variance` about zero.
    #[must_use]
    pub fn new(
        walk: f64,
        noise: f64,
        offset: f64,
        offset_variance: f64,
        rate_variance: f64,
    ) -> OffsetKalman {
        OffsetKalman {
            walk,
            noise,
            offset,
            rate: 0.0,
            covariance: [offset_variance, 0.0, rate_variance],
        }
    }

    /// Moves the estimate forward by `dt` seconds.
    pub fn predict(&mut self, dt: f64) {
        let [pxx, pxr, prr] = self.covariance;
        self.offset += self.rate * dt;
        self.covariance = [
            pxx + 2.0 * pxr * dt + prr * dt * dt + self.walk * dt.powi(3) / 3.0,
            pxr + prr * dt + self.walk * dt * dt / 2.0,
            prr + self.walk * dt,
        ];
    }

    /// Takes in a measurement of the offset at the current time.
    pub fn update(&mut self, measured: f64) {
        let [pxx, pxr, prr] = self.covariance;
        let innovation = measured - self.offset;
        let spread = pxx + self.noise;
        let (gain_offset, gain_rate) = (pxx / spread, pxr / spread);
        self.offset += gain_offset * innovation;
        self.rate += gain_rate * innovation;
        self.covariance = [
            pxx - gain_offset * pxx,
            pxr - gain_offset * pxr,
            prr - gain_rate * pxr,
        ];
    }

    /// The estimated offset at the current time.
    #[must_use]
    pub fn offset(&self) -> f64 {
        self.offset
    }

    /// The estimated rate.
    #[must_use]
    pub fn rate(&self) -> f64 {
        self.rate
    }
}

#[cfg(test)]
mod tests {
    use super::OffsetKalman;
    use crate::random::Generator;

    /// Without noise in the rate, the filter fits a line, and after many
    /// measurements of a line with noise it has found the line: with 10,000
    /// measurements of standard deviation 1 the offset is known to about
    /// 2 / sqrt(10,000) = 0.02.
    #[test]
    fn it_finds_a_line_through_noisy_measurements() {
        let mut filter = OffsetKalman::new(0.0, 1.0, 0.0, 1e6, 1e6);
        let mut generator = Generator::new(11);
        let (mut truth, rate, dt) = (5.0, 0.3, 0.1);
        for _ in 0..10_000 {
            truth += rate * dt;
            filter.predict(dt);
            filter.update(truth + generator.normal());
        }
        assert!(
            (filter.offset() - truth).abs() < 0.1,
            "offset error {}",
            filter.offset() - truth
        );
        assert!(
            (filter.rate() - rate).abs() < 1e-3,
            "rate error {}",
            filter.rate() - rate
        );
    }
}
