// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Deterministic seeded PRNG for reproducible simulations.

/// A generator of pseudo-random numbers (xoshiro256++), started from a seed.
///
/// Two generators with the same seed give the same numbers. Use
/// [`Generator::fork`] to give each simulated part its own stream, so that
/// adding a part does not change the numbers the others draw.
#[derive(Clone, Debug)]
pub struct Generator {
    state: [u64; 4],
}

impl Generator {
    /// A generator started from `seed`.
    #[must_use]
    pub fn new(seed: u64) -> Generator {
        // The state is filled by SplitMix64, as the authors of xoshiro advise.
        let mut x = seed;
        let mut next = || {
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        Generator {
            state: [next(), next(), next(), next()],
        }
    }

    /// A new generator whose numbers are unrelated to this one's, chosen by `label`.
    #[must_use]
    pub fn fork(&self, label: u64) -> Generator {
        Generator::new(
            self.state[0]
                ^ self.state[2].rotate_left(17)
                ^ label.wrapping_mul(0xd6e8_feb8_6659_fd93),
        )
    }

    /// The next 64 random bits.
    pub fn bits(&mut self) -> u64 {
        let [s0, s1, s2, s3] = self.state;
        let result = s0.wrapping_add(s3).rotate_left(23).wrapping_add(s0);
        let t = s1 << 17;
        let s2 = s2 ^ s0;
        let s3 = s3 ^ s1;
        let s1 = s1 ^ s2;
        let s0 = s0 ^ s3;
        self.state = [s0, s1, s2 ^ t, s3.rotate_left(45)];
        result
    }

    /// A number uniform in the open interval from 0 to 1.
    pub fn uniform(&mut self) -> f64 {
        // 53 random bits, moved half a step up so that 0 is never returned.
        #[allow(clippy::cast_precision_loss)]
        let value = ((self.bits() >> 11) as f64 + 0.5) / 9_007_199_254_740_992.0;
        value
    }

    /// `true` with probability `p`.
    pub fn chance(&mut self, p: f64) -> bool {
        self.uniform() < p
    }

    /// A number from the normal distribution with mean 0 and standard deviation 1.
    pub fn normal(&mut self) -> f64 {
        // Box and Muller's transform; the second number it yields is not kept.
        let radius = (-2.0 * self.uniform().ln()).sqrt();
        radius * (std::f64::consts::TAU * self.uniform()).cos()
    }

    /// A number from the exponential distribution with the given mean.
    pub fn exponential(&mut self, mean: f64) -> f64 {
        -mean * self.uniform().ln()
    }
}

#[cfg(test)]
mod tests {
    use super::Generator;

    #[test]
    fn the_same_seed_gives_the_same_numbers() {
        let (mut a, mut b) = (Generator::new(7), Generator::new(7));
        for _ in 0..100 {
            assert_eq!(a.bits(), b.bits());
        }
        assert_ne!(Generator::new(7).bits(), Generator::new(8).bits());
    }

    #[test]
    fn forks_with_different_labels_differ() {
        let parent = Generator::new(1);
        assert_ne!(parent.fork(1).bits(), parent.fork(2).bits());
        assert_eq!(parent.fork(1).bits(), parent.fork(1).bits());
    }

    /// With 200,000 draws the sample mean of a distribution with standard
    /// deviation 1 is within 0.01 of the true mean except with probability
    /// below one in 100,000, so a failure means a wrong distribution.
    #[test]
    fn the_distributions_have_their_stated_moments() {
        let n = 200_000;
        let mut g = Generator::new(42);
        let mean =
            |draw: &mut dyn FnMut() -> f64| (0..n).map(|_| draw()).sum::<f64>() / f64::from(n);
        let uniform = mean(&mut || g.uniform());
        assert!((uniform - 0.5).abs() < 0.01, "uniform mean {uniform}");
        let normal = mean(&mut || g.normal());
        assert!(normal.abs() < 0.01, "normal mean {normal}");
        let normal_square = mean(&mut || g.normal().powi(2));
        assert!(
            (normal_square - 1.0).abs() < 0.02,
            "normal variance {normal_square}"
        );
        let exponential = mean(&mut || g.exponential(3.0));
        assert!(
            (exponential - 3.0).abs() < 0.03,
            "exponential mean {exponential}"
        );
    }
}
