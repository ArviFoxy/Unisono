// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Positions in a stream and the step between two of them, as exact numbers.
//!
//! Re-exported from [`unisono_core::timing`] so the core regulator and the
//! resampler share one exact representation.

pub use unisono_core::timing::{Position, Step};
