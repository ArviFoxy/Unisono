// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fixed-point stream `Position` and `Step` types re-exported from
//! [`unisono_core::timing`] so the regulator and resampler share one exact
//! representation.

pub use unisono_core::timing::{Position, Step};
