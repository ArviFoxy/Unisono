// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The shell around unisono's core.
//!
//! The core decides; this crate does what the core cannot: it holds samples,
//! talks to audio systems, and moves frames. Its parts:
//!
//! - [`audio`]: what an audio system and unisono ask of each other, once for
//!   each cycle of a device;
//! - [`software`]: an audio device made of software, driven by a clock that
//!   its user sets;
//! - [`store`]: the samples of the frames that a receiver holds;
//! - [`pump`]: what turns the core's plan for a cycle into the frames that
//!   the device plays.

pub mod audio;
pub mod pump;
pub mod software;
pub mod store;
