/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Receiver.Adopt
public import Unisono.Receiver.Packet
public import Unisono.Receiver.Playback

/-!
# The receiver of a stream

Re-exports timeline adoption, packet ingestion and silence recovery, and
playhead/cycle/report proofs for `unisono_core::receiver`.
-/
