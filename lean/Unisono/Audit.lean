/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Analysis.Estimation
public import Unisono.Analysis.Level
public import Unisono.Analysis.ModalControl
public import Unisono.Analysis.Spectral
public import Unisono.Arrivals
public import Unisono.Blue
public import Unisono.Device
public import Unisono.Due
public import Unisono.Estimate
public import Unisono.Fixed
public import Unisono.Gains
public import Unisono.Kalman
public import Unisono.MinRtt
public import Unisono.Answers
public import Unisono.Model.Exchange
public import Unisono.Model.Gains
public import Unisono.Model.Level
public import Unisono.Model.LineFit
public import Unisono.Model.Regulation
public import Unisono.Model.RegulationRandom
public import Unisono.Model.Stream
public import Unisono.Model.SupportLine
public import Unisono.Needs
public import Unisono.Packet
public import Unisono.Player
public import Unisono.Presence
public import Unisono.Receiver
public import Unisono.Relation
public import Unisono.Rounds
public import Unisono.Sender
public import Unisono.Solutions.Core
public import Unisono.Solutions.FixedDelay.Exact
public import Unisono.Solutions.FixedDelay.Latency
public import Unisono.Solutions.FixedDelay.Memory
public import Unisono.Spec.AtLatency
public import Unisono.Spec.Checks
public import Unisono.Spec.ExactLatency
public import Unisono.Spec.Limits
public import Unisono.Spec.Models.Delays
public import Unisono.Spec.Models.GenerativeCanonical
public import Unisono.Spec.Models.GenerativeNoiseless
public import Unisono.Spec.Models.GenerativeWorld
public import Unisono.Spec.Models.Ideal
public import Unisono.Spec.Models.SecondOrder
public import Unisono.Spec.Models.StochasticWorld
public import Unisono.Spec.Optimality
public import Unisono.Spec.Run
public import Unisono.Spec.StarShift
public import Unisono.Spec.Topologies
public import Unisono.Sync

/-!
# The axioms the theorems rest on

Each theorem about a function of the core is listed here with the axioms its
proof uses. The three below are the standard axioms of Lean with classical
logic. The build fails if a list changes, which is how an axiom that enters
through the translation, or through an unfinished proof, is noticed.
-/

/-- info: 'Unisono.Fixed.saturate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.saturate_spec

/-- info: 'Unisono.Fixed.mul_shift_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.mul_shift_spec

/-- info: 'Unisono.Model.Exchange.error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Exchange.error_bound

/-- info: 'Unisono.Model.LineFit.cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.LineFit.cost_le

/-- info: 'Unisono.Model.LineFit.schedule_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.LineFit.schedule_invariant

/-- info: 'Unisono.Model.LineFit.error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.LineFit.error_bound

/-- info: 'Unisono.Model.SupportLine.highest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.SupportLine.highest

/-- info: 'Unisono.Model.SupportLine.error_at_centre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.SupportLine.error_at_centre

/-- info: 'Unisono.Relation.side_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.side_spec

/-- info: 'Unisono.Relation.is_under_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.is_under_spec

/-- info: 'Unisono.Relation.put_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.put_spec

/-- info: 'Unisono.Relation.drop_oldest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.drop_oldest_spec

/-- info: 'Unisono.Model.SupportLine.error_ahead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.SupportLine.error_ahead

/-- info: 'Unisono.Relation.forget_before_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.forget_before_spec

/-- info: 'Unisono.Relation.bridge_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.bridge_spec

/-- info: 'Unisono.Relation.limited_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.limited_spec

/-- info: 'Unisono.Relation.fit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.fit_spec

/-- info: 'Unisono.Relation.mean_time_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.mean_time_spec

/-- info: 'Unisono.Relation.through_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.through_best

/-- info: 'Unisono.Relation.through_excess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.through_excess

/-- info: 'Unisono.Relation.anchor_near_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.anchor_near_mean

/-- info: 'Unisono.Relation.observe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.observe_total

/-- info: 'Unisono.Relation.end_window_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.end_window_total

/-- info: 'Unisono.Packet.parse_audio_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_audio_total

/-- info: 'Unisono.Packet.write_audio_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_audio_total

/-- info: 'Unisono.Presence.width_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.width_spec

/-- info: 'Unisono.Presence.covers_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.covers_spec

/-- info: 'Unisono.Presence.held_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.held_spec

/-- info: 'Unisono.Presence.mark_frame_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.mark_frame_spec

/-- info: 'Unisono.Presence.mark_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.mark_spec

/-- info: 'Unisono.Presence.Arrived.comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.Arrived.comm

/-- info: 'Unisono.Presence.Arrived.again' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.Arrived.again

/-- info: 'Unisono.Presence.countOf_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.countOf_total

/-- info: 'Unisono.Presence.advance_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.advance_spec

/-- info: 'Unisono.Presence.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.run_spec

/-- info: 'Unisono.Presence.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.new_spec

/-- info: 'Unisono.Presence.gap_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.gap_spec

/-- info: 'Unisono.Presence.restart_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Presence.restart_spec

/-- info: 'Unisono.Receiver.packet_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.packet_spec

/-- info: 'Unisono.Receiver.follows_after_silence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.follows_after_silence

/-- info: 'Unisono.Receiver.take_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.take_spec

/-- info: 'Unisono.Receiver.take_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.take_idle

/-- info: 'Unisono.Receiver.skip_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.skip_spec

/-- info: 'Unisono.Receiver.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.new_spec

/-- info: 'Unisono.Sender.current_level_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.current_level_spec

/-- info: 'Unisono.Sender.levelAt_eq_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.levelAt_eq_floor

/-- info: 'Unisono.Sender.level_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.level_spec

/-- info: 'Unisono.Sender.packet_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.packet_spec

/-- info: 'Unisono.Sender.packet_ramp_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.packet_ramp_consistent

/-- info: 'Unisono.Sender.departed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.departed_spec

/-- info: 'Unisono.Sender.restart_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.restart_spec

/-- info: 'Unisono.Receiver.late_run_is_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.late_run_is_short

/-- info: 'Unisono.Receiver.restart_stores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.restart_stores

/-- info: 'Unisono.Receiver.cycle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.cycle_spec

/-- info: 'Unisono.Receiver.due_at_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.due_at_total

/-- info: 'Unisono.Due.due_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Due.due_spec

/-- info: 'Unisono.Model.Stream.dueTime_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Stream.dueTime_position

/-- info: 'Unisono.Player.cycle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.cycle_spec

/-- info: 'Unisono.Player.sender_time_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.sender_time_total

/-- info: 'Unisono.Player.due_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.due_total

/-- info: 'Unisono.Receiver.echo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.echo_spec

/-- info: 'Unisono.Receiver.report_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.report_spec

/-- info: 'Unisono.Receiver.reported_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.reported_spec

/-- info: 'Unisono.Packet.parse_report_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_report_total

/-- info: 'Unisono.Packet.write_report_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_report_total

/-- info: 'Unisono.Packet.parse_echo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_echo_total

/-- info: 'Unisono.Packet.write_echo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_echo_total

/-- info: 'Unisono.Sender.answer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sender.answer_spec

/-- info: 'Unisono.Device.observe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.observe_total

/-- info: 'Unisono.Device.when_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.when_total

/-- info: 'Unisono.Rounds.endsWithin_of_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.endsWithin_of_measure

/-- info: 'Unisono.Rounds.mark_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.mark_rounds

/-- info: 'Unisono.Rounds.run_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.run_rounds

/-- info: 'Unisono.Rounds.gap_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.gap_rounds

/-- info: 'Unisono.Rounds.advance_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.advance_rounds

/-- info: 'Unisono.Rounds.clear_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.clear_rounds

/-- info: 'Unisono.Rounds.find_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.find_rounds

/-- info: 'Unisono.Rounds.sums_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.sums_rounds

/-- info: 'Unisono.Player.cycle_step_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.cycle_step_small

/-- info: 'Unisono.Player.gain_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.gain_spec

/-- info: 'Unisono.Player.gains_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.gains_spec

/-- info: 'Unisono.Player.regulate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.regulate_spec

/-- info: 'Unisono.Model.Gains.gains_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Gains.gains_close

/-- info: 'Unisono.Model.Gains.gains_of_integers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Gains.gains_of_integers

/-- info: 'Unisono.Model.Gains.law_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Gains.law_close

/-- info: 'Unisono.Model.Gains.planned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Gains.planned

/-- info: 'Unisono.Model.Gains.cost_of_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Gains.cost_of_distance

/-- info: 'Unisono.Fixed.div_floor_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.div_floor_spec

/-- info: 'Unisono.Fixed.div_floor_wide_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.div_floor_wide_spec

/-- info: 'Unisono.Fixed.root_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.root_spec

/-- info: 'Unisono.Device.observe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.observe_spec

/-- info: 'Unisono.Device.when_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.when_spec

/-- info: 'Unisono.Device.beyondZ_eq_floor_lineFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.beyondZ_eq_floor_lineFit

/-- info: 'Unisono.Arrivals.find_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Arrivals.find_spec

/-- info: 'Unisono.Arrivals.record_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Arrivals.record_spec

/-- info: 'Unisono.Packet.read_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.read_spec

/-- info: 'Unisono.Packet.write_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_spec

/-- info: 'Unisono.Packet.payload_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.payload_spec

/-- info: 'Unisono.Packet.validate_audio_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.validate_audio_spec

/-- info: 'Unisono.Packet.parse_audio_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_audio_valid

/-- info: 'Unisono.Packet.write_audio_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_audio_spec

/-- info: 'Unisono.Packet.audio_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.audio_roundtrip

/-- info: 'Unisono.Packet.write_report_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_report_spec

/-- info: 'Unisono.Packet.report_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.report_roundtrip

/-- info: 'Unisono.Packet.write_echo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_echo_spec

/-- info: 'Unisono.Packet.echo_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.echo_roundtrip

/-- info: 'Unisono.Packet.write_request_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_request_spec

/-- info: 'Unisono.Packet.request_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.request_roundtrip

/-- info: 'Unisono.Packet.parse_request_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_request_total

/-- info: 'Unisono.Packet.write_request_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_request_total

/-- info: 'Unisono.Packet.parse_request_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_request_kind

/-- info: 'Unisono.Packet.kind_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.kind_spec

/-- info: 'Unisono.Packet.parse_audio_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_audio_kind

/-- info: 'Unisono.Packet.parse_report_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_report_kind

/-- info: 'Unisono.Packet.parse_echo_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_echo_kind

/-- info: 'Unisono.Relation.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.new_spec

/-- info: 'Unisono.Relation.remember_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.remember_spec

/-- info: 'Unisono.Relation.reset_window_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.reset_window_spec

/-- info: 'Unisono.Relation.observe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.observe_spec

/-- info: 'Unisono.Receiver.adopt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.adopt_spec

/-- info: 'Unisono.Receiver.keep_newest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.keep_newest_spec

/-- info: 'Unisono.Receiver.wrong_stream_packet_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.wrong_stream_packet_noop

/-- info: 'Unisono.Receiver.wrong_stream_echo_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.wrong_stream_echo_noop

/-- info: 'Unisono.Receiver.single_stray_timeline_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.single_stray_timeline_noop

/-- info: 'Unisono.Player.step_clamped_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.step_clamped_spec

/-- info: 'Unisono.Device.when_cycle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.when_cycle_spec

/-- info: 'Unisono.Device.beyondSlopeQ16Z_eq_floor_lineFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.beyondSlopeQ16Z_eq_floor_lineFit

/-- info: 'Unisono.Relation.overtaken_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.overtaken_spec

/-- info: 'Unisono.Relation.consider_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.consider_spec

/-- info: 'Unisono.Relation.observe_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.observe_later

/-- info: 'Unisono.Relation.observe_in_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.observe_in_order

/-- info: 'Unisono.Player.position_units_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.position_units_total

/-- info: 'Unisono.Player.position_from_units_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.position_from_units_total

/-- info: 'Unisono.Player.step_units_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.step_units_total

/-- info: 'Unisono.Player.step_new_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.step_new_total

/-- info: 'Unisono.Player.position_advance_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.position_advance_total

/-- info: 'Unisono.Player.step_from_parts_per_billion_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.step_from_parts_per_billion_total

/-- info: 'Unisono.Device.push_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.push_spec

/-- info: 'Unisono.Device.start_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.start_spec

/-- info: 'Unisono.Device.shift_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.shift_spec

/-- info: 'Unisono.Device.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.step_spec

/-- info: 'Unisono.Device.observe_after_aside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.observe_after_aside

/-- info: 'Unisono.Answers.observe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Answers.observe_total

/-- info: 'Unisono.Answers.shortest_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Answers.shortest_total

/-- info: 'Unisono.Answers.new_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Answers.new_total

/-- info: 'Unisono.Needs.new_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Needs.new_total

/-- info: 'Unisono.Needs.clear_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Needs.clear_total

/-- info: 'Unisono.Needs.observe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Needs.observe_total

/-- info: 'Unisono.Needs.newest_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Needs.newest_total

/-- info: 'Unisono.Needs.get_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Needs.get_total

/-- info: 'Unisono.Needs.recent_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Needs.recent_total

/-- info: 'Unisono.Packet.write_needs_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_needs_total

/-- info: 'Unisono.Packet.parse_needs_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_needs_total

/-- info: 'Unisono.Model.Regulation.cost_add_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.cost_add_value

/-- info: 'Unisono.Model.Regulation.value_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.value_step

/-- info: 'Unisono.Model.Regulation.total_cost_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.total_cost_ge

/-- info: 'Unisono.Model.Regulation.total_cost_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.total_cost_law

/-- info: 'Unisono.Model.Regulation.weight_gainFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.weight_gainFor

/-- info: 'Unisono.Model.Regulation.gain_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.gain_unique

/-- info: 'Unisono.Model.RegulationRandom.mean_cost_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.mean_cost_sum

/-- info: 'Unisono.Model.RegulationRandom.mean_cost_law_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.mean_cost_law_le

/-- info: 'Unisono.Model.RegulationRandom.unforeseen_revision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.unforeseen_revision

/-- info: 'Unisono.Model.RegulationRandom.mean_square_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.mean_square_split

/-- info: 'Unisono.Model.Regulation.distance_from_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.distance_from_rest

/-- info: 'Unisono.Model.Regulation.next_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.next_shift

/-- info: 'Unisono.Model.Regulation.at_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulation.at_limit

/-- info: 'Unisono.Model.Level.measure_largest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.measure_largest

/-- info: 'Unisono.Model.Level.integral_predictive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.integral_predictive

/-- info: 'Unisono.Model.Level.volume_missed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.volume_missed

/-- info: 'Unisono.Model.Level.missed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.missed_le

/-- info: 'Unisono.Model.Level.missed_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.missed_ge

/-- info: 'Unisono.Model.Level.volume_lasts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.volume_lasts

/-- info: 'Unisono.Model.Level.move_pays_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.move_pays_iff

/-- info: 'Unisono.Model.SupportLine.estimate_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.SupportLine.estimate_isGreatest

/-- info: 'Unisono.Model.SupportLine.excess_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.SupportLine.excess_le

/-- info: 'Unisono.Model.SupportLine.excess_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.SupportLine.excess_near

/-- info: 'Unisono.Model.Stream.group_misses_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Stream.group_misses_iff

/-- info: 'Unisono.Model.Stream.sum_sq_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Stream.sum_sq_errors

/-- info: 'Unisono.Model.Stream.groupNeed_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Stream.groupNeed_errors

/-- info: 'Unisono.Model.Stream.group_misses_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Stream.group_misses_errors

/-- info: 'Unisono.Model.RegulationRandom.mean_value_law_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.mean_value_law_le

/-- info: 'Unisono.Model.RegulationRandom.mean_cost_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.mean_cost_rate

/-- info: 'Unisono.Model.RegulationRandom.distance_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.distance_step

/-- info: 'Unisono.Model.RegulationRandom.unforeseen_pace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.RegulationRandom.unforeseen_pace

/-- info: 'Unisono.Fixed.rem_euclid_wide_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.rem_euclid_wide_spec

/-- info: 'Unisono.Due.dueUnits_eq_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Due.dueUnits_eq_floor

/-- info: 'Unisono.Relation.slope_within_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.slope_within_spec

/-- info: 'Unisono.Relation.eval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.eval_spec

/-- info: 'Unisono.Relation.append_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.append_spec

/-- info: 'Unisono.Relation.keep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.keep_spec

/-- info: 'Unisono.Relation.end_window_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Relation.end_window_spec

/-- info: 'Unisono.Device.fit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Device.fit_spec

/-- info: 'Unisono.Rounds.shift_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Rounds.shift_rounds

/-- info: 'Unisono.Answers.clear_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Answers.clear_spec

/-- info: 'Unisono.Model.Level.measure_largest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Level.measure_largest_le

/-! ## Checks of the specification's definitions -/

/-- info: 'Unisono.Spec.speed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.speed_eq

/-- info: 'Unisono.Spec.missedAt_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_none

/-- info: 'Unisono.Spec.missedAt_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_after

/-- info: 'Unisono.Spec.missedAt_continues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_continues

/-- info: 'Unisono.Spec.missedAt_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_skip

/-- info: 'Unisono.Spec.missedAt_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_repeat

/-- info: 'Unisono.Spec.missedAt_after_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_after_gap

/-- info: 'Unisono.Spec.missedAt_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_resume

/-- info: 'Unisono.Spec.sum_pairs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_pairs_eq

/-- info: 'Unisono.Spec.Solution.eventTime_le_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.eventTime_le_succ

/-- info: 'Unisono.Spec.Solution.decided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.decided

/-- info: 'Unisono.Spec.Link.deliver_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Link.deliver_after

/-- info: 'Unisono.Spec.discontinuities_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuities_gap

/-- info: 'Unisono.Spec.discontinuityAt_jump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuityAt_jump

/-- info: 'Unisono.Spec.roughnessCost_across' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.roughnessCost_across

/-- info: 'Unisono.Spec.latencyCost_unplayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.latencyCost_unplayed

/-- info: 'Unisono.Spec.syncCost_one_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.syncCost_one_off

/-- info: 'Unisono.Spec.Bounds.example_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Bounds.example_within

/-- info: 'Unisono.Spec.IdealConstantWorld.withinBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.withinBounds

/-- info: 'Unisono.Spec.IdealConstantWorld.example_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.example_holds

/-- info: 'Unisono.Spec.StationaryNetworkDisturbances.example_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StationaryNetworkDisturbances.example_holds

/-- info: 'Unisono.Spec.StochasticWorld.Holds.network_random' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StochasticWorld.Holds.network_random

/-- info: 'Unisono.Spec.StochasticWorld.example_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StochasticWorld.example_holds

/-- info: 'Unisono.Spec.OptimalWithin.expectedCost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.OptimalWithin.expectedCost_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.leastDelay_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.leastDelay_pos

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.leastDelay_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.leastDelay_add

/-- info: 'Unisono.Spec.GenerativeWorld.trafficLaw_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.trafficLaw_univ

/-- info: 'Unisono.Spec.GenerativeWorld.betaPDF_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.betaPDF_one_sub

/-- info: 'Unisono.Spec.GenerativeWorld.betaMeasure_map_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.betaMeasure_map_one_sub

/-- info: 'Unisono.Spec.GenerativeWorld.betaMeasure_compl_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.betaMeasure_compl_Ioo

/-- info: 'Unisono.Spec.GenerativeWorld.trafficLaw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.trafficLaw_zero

/-- info: 'Unisono.Spec.GenerativeWorld.example_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.example_holds

/-- info: 'Unisono.Spec.World.finite_hosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.finite_hosts

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.logRate_ae_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.logRate_ae_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.wander_ae_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.wander_ae_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.traffic_ae_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.traffic_ae_const

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.isBacklog_zero_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.isBacklog_zero_of_const

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.reading_of_noiseless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.reading_of_noiseless

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_idealConstantWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_idealConstantWorld

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_withinBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_withinBounds

/-- info: 'Unisono.Spec.limsup_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limsup_weighted

/-- info: 'Unisono.Spec.World.cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.cost_le

/-- info: 'Unisono.Spec.World.weighted_tracking_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.weighted_tracking_le_cost

/-- info: 'Unisono.Spec.World.PlaysAtLatencies.playsAtLatency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.PlaysAtLatencies.playsAtLatency

/-- info: 'Unisono.Spec.World.missed_eq_zero_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.missed_eq_zero_of_exact

/-- info: 'Unisono.Spec.World.discontinuities_eq_zero_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.discontinuities_eq_zero_of_exact

/-- info: 'Unisono.Spec.World.latency_eq_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.latency_eq_of_exact

/-- info: 'Unisono.Spec.World.capture_step_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.capture_step_of_linear

/-- info: 'Unisono.Spec.World.tracking_le_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.tracking_le_of_exact

/-- info: 'Unisono.Spec.World.sync_le_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sync_le_of_exact

/-- info: 'Unisono.Spec.IdealConstantWorld.Holds.captured_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.Holds.captured_eq

/-- info: 'Unisono.Spec.Solution.plays_shiftStarKeepPeers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_shiftStarKeepPeers

/-- info: 'Unisono.Spec.IdealConstantWorld.Holds.starNet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.Holds.starNet

/-- info: 'Unisono.Spec.IdealConstantWorld.Holds.shiftStarKeepPeers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.Holds.shiftStarKeepPeers

/-- info: 'Unisono.Solutions.FixedDelay.latencyError_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.latencyError_ideal

/-- info: 'Unisono.Solutions.FixedDelay.cost_le_of_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.cost_le_of_ideal

/-- info: 'Unisono.Spec.shiftCost_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.shiftCost_nonneg

/-- info: 'Unisono.Spec.frameCost_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.frameCost_nonneg

/-- info: 'Unisono.Spec.meanFin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.meanFin_add

/-- info: 'Unisono.Spec.meanFin_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.meanFin_sub

/-- info: 'Unisono.Spec.varFin_add_add_varFin_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.varFin_add_add_varFin_sub

/-- info: 'Unisono.Spec.two_mul_shiftCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.two_mul_shiftCost_le

/-- info: 'Unisono.Spec.World.accruedFrames_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.accruedFrames_mono

/-- info: 'Unisono.Spec.World.accruedFrames_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.accruedFrames_weighted

/-- info: 'Unisono.Spec.World.longRun_frames_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.longRun_frames_le_cost

/-- info: 'Unisono.Spec.playTime_shiftStarKeepPeers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.playTime_shiftStarKeepPeers

/-- info: 'Unisono.Spec.Solution.cost_shiftStarKeepPeers_add_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.cost_shiftStarKeepPeers_add_ge

/-- info: 'Unisono.Spec.iIndepFun_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.iIndepFun_of_const

/-- info: 'Unisono.Spec.isGaussianProcess_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.isGaussianProcess_zero

/-- info: 'Unisono.Spec.GenerativeWorld.splitOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.splitOf_mem

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_splitOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_splitOf

/-- info: 'Unisono.Spec.GenerativeWorld.splitOf_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.splitOf_ae_eq

/-- info: 'Unisono.Spec.GenerativeWorld.splitOf_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.splitOf_one_sub

/-- info: 'Unisono.Spec.GenerativeWorld.pairOf_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pairOf_swap

/-- info: 'Unisono.Spec.GenerativeWorld.refOrientation_pairOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.refOrientation_pairOf

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalDraw_split_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalDraw_split_mem

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalDraw_split_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalDraw_split_swap

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_canonicalMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_canonicalMap

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalDraw_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalDraw_component

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalDraw_split_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalDraw_split_law

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalDraw_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalDraw_prior

/-- info: 'Unisono.Spec.GenerativeWorld.idealWorld_builds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.idealWorld_builds

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalWorld_builds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalWorld_builds

/-- info: 'Unisono.Spec.GenerativeWorld.exists_holds_of_noiseless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.exists_holds_of_noiseless

/-- info: 'Unisono.Spec.longRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.longRun_le

/-- info: 'Unisono.Spec.missed_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missed_eq_zero

/-- info: 'Unisono.Spec.discontinuities_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuities_eq_zero

/-- info: 'Unisono.Spec.meanLatency_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.meanLatency_le

/-- info: 'Unisono.Spec.sync_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sync_le

/-- info: 'Unisono.Spec.tracking_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.tracking_le

/-- info: 'Unisono.Spec.Solution.held_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.held_mono

/-- info: 'Unisono.Spec.Solution.frames_arrive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.frames_arrive

/-- info: 'Unisono.Spec.State.sendAll_delivered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.sendAll_delivered

/-- info: 'Unisono.Spec.Solution.exists_handed_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.exists_handed_step

/-- info: 'Unisono.Spec.State.handle_delivered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.handle_delivered

/-- info: 'Unisono.Solutions.FixedDelay.block_arrives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_arrives

/-- info: 'Unisono.Spec.Solution.mem_inFlight_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.mem_inFlight_succ

/-- info: 'Unisono.Spec.Solution.views_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.views_succ

/-- info: 'Unisono.Solutions.FixedDelay.origin_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.origin_inFlight

/-- info: 'Unisono.Spec.offset_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.offset_error

/-- info: 'Unisono.Spec.offset_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.offset_drift

/-- info: 'Unisono.Spec.Solution.handled_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_before

/-- info: 'Unisono.Spec.Solution.handled_of_mem_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_of_mem_views

/-- info: 'Unisono.Solutions.FixedDelay.advance_tracks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.advance_tracks

/-- info: 'Unisono.Solutions.FixedDelay.block_received' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_received

/-- info: 'Unisono.Solutions.FixedDelay.block_latest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_latest

/-- info: 'Unisono.Solutions.FixedDelay.offset_received' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.offset_received

/-- info: 'Unisono.Solutions.FixedDelay.offset_latest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.offset_latest

/-- info: 'Unisono.Solutions.FixedDelay.asked_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.asked_request

/-- info: 'Unisono.Solutions.FixedDelay.last_after_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.last_after_request

/-- info: 'Unisono.Solutions.FixedDelay.last_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.last_none

/-- info: 'Unisono.Solutions.FixedDelay.answered_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.answered_query

/-- info: 'Unisono.Solutions.FixedDelay.answered_latest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.answered_latest

/-- info: 'Unisono.Spec.Solution.sent_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.sent_inFlight

/-- info: 'Unisono.Spec.Solution.copy_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.copy_inFlight

/-- info: 'Unisono.Solutions.FixedDelay.replicate_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.replicate_copies

/-- info: 'Unisono.Solutions.FixedDelay.query_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.query_inFlight

/-- info: 'Unisono.Solutions.FixedDelay.answer_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.answer_inFlight

/-- info: 'Unisono.Solutions.FixedDelay.query_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.query_answered

/-- info: 'Unisono.Solutions.FixedDelay.answer_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.answer_reaches

/-- info: 'Unisono.Solutions.FixedDelay.offset_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.offset_sample

/-- info: 'Unisono.Spec.Solution.handled_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_time

/-- info: 'Unisono.Spec.Solution.eventTime_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.eventTime_mono

/-- info: 'Unisono.Spec.Solution.handled_of_views_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_of_views_eq

/-- info: 'Unisono.Solutions.FixedDelay.solution_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.solution_append

/-- info: 'Unisono.Spec.Clock.read_sub_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Clock.read_sub_near

/-- info: 'Unisono.Spec.offset_drift_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.offset_drift_abs

/-- info: 'Unisono.Spec.CaptureDevice.capture_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.capture_sub_mem

/-- info: 'Unisono.Spec.PlaybackDevice.out_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.out_sub_mem

/-- info: 'Unisono.Spec.World.captured_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.captured_sub_mem

/-- info: 'Unisono.Spec.World.exists_captured_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.exists_captured_eq

/-- info: 'Unisono.Spec.World.sub_le_of_captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sub_le_of_captured

/-- info: 'Unisono.Solutions.FixedDelay.target_time_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.target_time_error

/-- info: 'Unisono.Solutions.FixedDelay.positions_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.positions_fold

/-- info: 'Unisono.Solutions.FixedDelay.lookup_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.lookup_chosen

/-- info: 'Unisono.Solutions.FixedDelay.positions_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.positions_block

/-- info: 'Unisono.Solutions.FixedDelay.lastChosen_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.lastChosen_block

/-- info: 'Unisono.Solutions.FixedDelay.chosen_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.chosen_succ

/-- info: 'Unisono.Solutions.FixedDelay.chosen_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.chosen_isSome

/-- info: 'Unisono.Solutions.FixedDelay.advance_converges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.advance_converges

/-- info: 'Unisono.Spec.Solution.askedNext_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.askedNext_mono

/-- info: 'Unisono.Spec.Solution.exists_asked_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.exists_asked_step

/-- info: 'Unisono.Spec.Solution.plays_of_asked_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_of_asked_step

/-- info: 'Unisono.Spec.Solution.handled_of_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_of_asked

/-- info: 'Unisono.Spec.Solution.handled_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_asked

/-- info: 'Unisono.Spec.Solution.askedNext_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.askedNext_succ

/-- info: 'Unisono.Spec.Solution.views_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.views_append

/-- info: 'Unisono.Spec.Solution.no_request_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.no_request_between

/-- info: 'Unisono.Solutions.FixedDelay.last_at_next_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.last_at_next_request

/-- info: 'Unisono.Solutions.FixedDelay.block_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_handled

/-- info: 'Unisono.Solutions.FixedDelay.block_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_memory

/-- info: 'Unisono.Solutions.FixedDelay.offset_recent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.offset_recent

/-- info: 'Unisono.Solutions.FixedDelay.captured_nominal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.captured_nominal

/-- info: 'Unisono.Solutions.FixedDelay.captured_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.captured_target

/-- info: 'Unisono.Solutions.FixedDelay.exists_block_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exists_block_of_frame

/-- info: 'Unisono.Solutions.FixedDelay.frame_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.frame_held

/-- info: 'Unisono.Solutions.FixedDelay.playable_of_captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.playable_of_captured

/-- info: 'Unisono.Spec.Solution.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.progress

/-- info: 'Unisono.Spec.CaptureDevice.handed_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.handed_unbounded

/-- info: 'Unisono.Spec.PlaybackDevice.asked_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.asked_unbounded

/-- info: 'Unisono.Solutions.FixedDelay.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.progress

/-- info: 'Unisono.Solutions.FixedDelay.asked_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.asked_gap

/-- info: 'Unisono.Solutions.FixedDelay.handed_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.handed_gap

/-- info: 'Unisono.Solutions.FixedDelay.request_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.request_step

/-- info: 'Unisono.Solutions.FixedDelay.target_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.target_band

/-- info: 'Unisono.Solutions.FixedDelay.exists_last_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exists_last_below

/-- info: 'Unisono.Solutions.FixedDelay.exists_block_of_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exists_block_of_sample

/-- info: 'Unisono.Solutions.FixedDelay.trajectory_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.trajectory_step

/-- info: 'Unisono.Spec.World.captured_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.captured_lipschitz

/-- info: 'Unisono.Solutions.FixedDelay.plays_eq_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.plays_eq_chosen

/-- info: 'Unisono.Solutions.FixedDelay.targetError_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.targetError_mono

/-- info: 'Unisono.Solutions.FixedDelay.late_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.late_targets

/-- info: 'Unisono.Solutions.FixedDelay.speaker_at_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.speaker_at_latency

/-- info: 'Unisono.Solutions.FixedDelay.plays_at_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.plays_at_latency

/-- info: 'Unisono.Solutions.FixedDelay.guarantees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.guarantees

/-- info: 'Unisono.Solutions.FixedDelay.plays_at_latency_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.plays_at_latency_example

/-- info: 'Unisono.Spec.ClockNoise.density_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ClockNoise.density_nonneg

/-- info: 'Unisono.Spec.secondDifferenceCovariance_integrableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.secondDifferenceCovariance_integrableOn

/-- info: 'Unisono.Spec.secondDifferenceCovariance_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.secondDifferenceCovariance_diag_le

/-- info: 'Unisono.Spec.SecondOrderMoments.example_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.SecondOrderMoments.example_holds

/-- info: 'Unisono.Spec.modal_sq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.modal_sq_split

/-- info: 'Unisono.Spec.World.syncCost_eq_var' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.syncCost_eq_var

/-- info: 'Unisono.Spec.World.trackingCost_eq_sync_add_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.trackingCost_eq_sync_add_mean

/-- info: 'Unisono.Spec.World.weighted_frame_modal_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.weighted_frame_modal_split

/-- info: 'Unisono.Spec.World.roughness_linear_ramp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.roughness_linear_ramp

/-- info: 'Unisono.Spec.World.roughness_boundary_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.roughness_boundary_step

/-- info: 'Unisono.Spec.cyclePositionWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.cyclePositionWeight_eq

/-- info: 'Unisono.Spec.World.shiftHosts_rtt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.shiftHosts_rtt_eq

/-- info: 'Unisono.Spec.Solution.plays_shiftHosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_shiftHosts

/-- info: 'Unisono.Spec.Solution.sync_shiftHosts_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.sync_shiftHosts_lower_bound

/-- info: 'Unisono.Spec.Solution.tracking_shiftHosts_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.tracking_shiftHosts_lower_bound

/-! ## Analysis and fundamental limits -/

/-- info: 'Unisono.Analysis.weight_gainForWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.weight_gainForWeight

/-- info: 'Unisono.Analysis.gainForWeight_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.gainForWeight_unique

/-- info: 'Unisono.Analysis.single_cost_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.single_cost_split

/-- info: 'Unisono.Analysis.single_law_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.single_law_optimal

/-- info: 'Unisono.Analysis.single_law_unique_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.single_law_unique_ae

/-- info: 'Unisono.Analysis.multiCycleCost_modal_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multiCycleCost_modal_split

/-- info: 'Unisono.Analysis.multi_lipsync_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_optimal

/-- info: 'Unisono.Analysis.multi_lipsync_unique_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_unique_ae

/-- info: 'Unisono.Analysis.multi_lipsync_cost_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_cost_rate

/-- info: 'Unisono.Analysis.multi_lipsync_law_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_law_cost_le

/-- info: 'Unisono.Analysis.multi_lowlatency_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lowlatency_optimal

/-- info: 'Unisono.Analysis.multi_lowlatency_unique_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lowlatency_unique_ae

/-- info: 'Unisono.Analysis.decentralized_star_cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.decentralized_star_cost_eq

/-- info: 'Unisono.Analysis.symmetric_star_cost_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.symmetric_star_cost_split

/-- info: 'Unisono.Analysis.decentralized_star_uncorrelated_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.decentralized_star_uncorrelated_optimal

/-- info: 'Unisono.Analysis.consensus_one_hot_var' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.consensus_one_hot_var

/-- info: 'Unisono.Analysis.weight_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.weight_factor

/-- info: 'Unisono.Analysis.step_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.step_step

/-- info: 'Unisono.Analysis.butterworth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.butterworth

/-- info: 'Unisono.Analysis.filterRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.filterRoot_eq

/-- info: 'Unisono.Analysis.filterRoot_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.filterRoot_unique

/-- info: 'Unisono.Analysis.estimate_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.estimate_factor

/-- info: 'Unisono.Analysis.riccati_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.riccati_fixed

/-- info: 'Unisono.Analysis.posterior_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.posterior_variance

/-- info: 'Unisono.Analysis.revision_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.revision_variance

/-- info: 'Unisono.Analysis.clockProcessCov_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.clockProcessCov_nonneg

/-- info: 'Unisono.Analysis.star_pair_error_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.star_pair_error_same

/-- info: 'Unisono.Analysis.star_pair_error_heterogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.star_pair_error_heterogeneous

/-- info: 'Unisono.Analysis.disciplined_schedule_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.disciplined_schedule_error

/-- info: 'Unisono.Analysis.residual_variance_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.residual_variance_sub

/-- info: 'Unisono.Analysis.residual_variance_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.residual_variance_L2

/-- info: 'Unisono.Analysis.linear_unbiased_iff_unitFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.linear_unbiased_iff_unitFlow

/-- info: 'Unisono.Analysis.graph_estimator_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.graph_estimator_bias

/-- info: 'Unisono.Analysis.thomson_blue_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.thomson_blue_optimal

/-- info: 'Unisono.Analysis.star_effective_resistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.star_effective_resistance

/-- info: 'Unisono.Analysis.complete_graph_effective_resistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.complete_graph_effective_resistance

/-- info: 'Unisono.Analysis.complete_graph_equal_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.complete_graph_equal_budget

/-- info: 'Unisono.Analysis.wifi_sender_wired_peers_resistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.wifi_sender_wired_peers_resistance

/-- info: 'Unisono.Analysis.triangle_blue_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.triangle_blue_bias

/-- info: 'Unisono.Analysis.margin_best_missed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.margin_best_missed

/-- info: 'Unisono.Analysis.margin_best_tracking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.margin_best_tracking

/-- info: 'Unisono.Analysis.fleet_average_missed_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.fleet_average_missed_cost

/-- info: 'Unisono.Analysis.margin_best_exponential_with_clicks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.margin_best_exponential_with_clicks

/-- info: 'Unisono.Analysis.discontinuity_nonconvex_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.discontinuity_nonconvex_example

/-- info: 'Unisono.Spec.withinSpeed_of_step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.withinSpeed_of_step_bound

/-- info: 'Unisono.Spec.fixedDelay_isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.fixedDelay_isStar

/-- info: 'Unisono.Spec.star_states_eq_of_star_links_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.star_states_eq_of_star_links_eq

/-- info: 'Unisono.Spec.star_sync_lower_bound_with_symmetric_peers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.star_sync_lower_bound_with_symmetric_peers

/-- info: 'Unisono.Spec.peer_probe_recovers_exact_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.peer_probe_recovers_exact_offset

/-- info: 'Unisono.Spec.PeerSync.usesGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PeerSync.usesGraph

/-- info: 'Unisono.Spec.PeerSync.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PeerSync.progress

/-- info: 'Unisono.Spec.PeerSync.sync_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PeerSync.sync_eq_zero

/-- info: 'Unisono.Spec.peer_beats_star_asymmetry_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.peer_beats_star_asymmetry_bound

/-- info: 'Unisono.Spec.FixedDelay.noCrossOriginCollision_sepBaseWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.FixedDelay.noCrossOriginCollision_sepBaseWorld

/-- info: 'Unisono.Spec.ForwardStar.isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ForwardStar.isStar

/-- info: 'Unisono.Spec.ForwardStar.noCrossOriginCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ForwardStar.noCrossOriginCollision

/-- info: 'Unisono.Spec.ForwardStar.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ForwardStar.progress

/-- info: 'Unisono.Spec.ForwardStar.sync_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ForwardStar.sync_eq

/-! ## Production v2 core proofs and `Unisono.Solutions.Core` -/

/-- info: 'Unisono.Fixed.saturating_mul_i128_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.saturating_mul_i128_spec

/-- info: 'Unisono.Fixed.saturating_mul_i64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.saturating_mul_i64_spec

/-- info: 'Unisono.Fixed.scale_div_pow2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.scale_div_pow2_spec

/-- info: 'Unisono.Packet.write_peer_probe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_peer_probe_spec

/-- info: 'Unisono.Packet.peer_probe_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.peer_probe_roundtrip

/-- info: 'Unisono.Packet.parse_peer_probe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_peer_probe_total

/-- info: 'Unisono.Packet.write_peer_probe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_peer_probe_total

/-- info: 'Unisono.Packet.parse_peer_probe_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_peer_probe_kind

/-- info: 'Unisono.Packet.write_peer_echo_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_peer_echo_spec

/-- info: 'Unisono.Packet.peer_echo_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.peer_echo_roundtrip

/-- info: 'Unisono.Packet.parse_peer_echo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_peer_echo_total

/-- info: 'Unisono.Packet.write_peer_echo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_peer_echo_total

/-- info: 'Unisono.Packet.parse_peer_echo_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_peer_echo_kind

/-- info: 'Unisono.Packet.parse_peer_relay_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_peer_relay_total

/-- info: 'Unisono.Packet.write_peer_relay_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.write_peer_relay_total

/-- info: 'Unisono.Packet.parse_peer_relay_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Packet.parse_peer_relay_kind

/-- info: 'Unisono.MinRtt.ntp_exchange_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.ntp_exchange_spec

/-- info: 'Unisono.MinRtt.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.new_spec

/-- info: 'Unisono.MinRtt.reset_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.reset_spec

/-- info: 'Unisono.MinRtt.observe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.observe_spec

/-- info: 'Unisono.MinRtt.path_ns_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.path_ns_spec

/-- info: 'Unisono.MinRtt.variance_ns2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.variance_ns2_spec

/-- info: 'Unisono.MinRtt.uncalibrated_variance_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.MinRtt.uncalibrated_variance_spec

/-- info: 'Unisono.Kalman.enforce_psd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.enforce_psd_spec

/-- info: 'Unisono.Kalman.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.new_spec

/-- info: 'Unisono.Kalman.anchor_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.anchor_spec

/-- info: 'Unisono.Kalman.anchor_with_freq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.anchor_with_freq_spec

/-- info: 'Unisono.Kalman.predict_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.predict_psd

/-- info: 'Unisono.Kalman.update_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.update_psd

/-- info: 'Unisono.Kalman.to_line_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.to_line_spec

/-- info: 'Unisono.Kalman.predict_zero_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.predict_zero_fixed_point

/-- info: 'Unisono.Kalman.update_zero_innovation_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.update_zero_innovation_fixed_point

/-- info: 'Unisono.Kalman.to_line_zero_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Kalman.to_line_zero_fixed_point

/-- info: 'Unisono.Blue.solve_ldlt_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Blue.solve_ldlt_total

/-- info: 'Unisono.Blue.solve_ldlt_zero_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Blue.solve_ldlt_zero_rhs

/-- info: 'Unisono.Blue.solve_blue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Blue.solve_blue_spec

/-- info: 'Unisono.Blue.solve_blue_single_edge_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Blue.solve_blue_single_edge_star

/-- info: 'Unisono.Player.modal_cycle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.modal_cycle_spec

/-- info: 'Unisono.Player.modal_cycle_step_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.modal_cycle_step_small

/-- info: 'Unisono.Player.modal_star_matches_player' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.modal_star_matches_player

/-- info: 'Unisono.Sync.new_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.new_total

/-- info: 'Unisono.Sync.add_peer_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.add_peer_total

/-- info: 'Unisono.Sync.on_sender_echo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.on_sender_echo_total

/-- info: 'Unisono.Sync.next_peer_probe_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.next_peer_probe_total

/-- info: 'Unisono.Sync.on_peer_probe_allowlist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.on_peer_probe_allowlist

/-- info: 'Unisono.Sync.on_peer_echo_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.on_peer_echo_total

/-- info: 'Unisono.Sync.build_relay_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.build_relay_total

/-- info: 'Unisono.Sync.on_peer_relay_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.on_peer_relay_total

/-- info: 'Unisono.Sync.publish_star_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.publish_star_spec

/-- info: 'Unisono.Sync.step_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.step_total

/-- info: 'Unisono.Sync.set_sender_clock_id_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.set_sender_clock_id_total

/-- info: 'Unisono.Sync.reset_sender_clock_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.reset_sender_clock_total

/-- info: 'Unisono.Sync.update_modal_filters_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.update_modal_filters_total

/-- info: 'Unisono.Sync.zero_peers_no_peer_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.zero_peers_no_peer_traffic

/-- info: 'Unisono.Sync.step_zero_peers_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Sync.step_zero_peers_star

/-- info: 'Unisono.Solutions.Core.usesGraph_of_peers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.usesGraph_of_peers

/-- info: 'Unisono.Solutions.Core.isStar_of_no_peers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.isStar_of_no_peers

/-- info: 'Unisono.Solutions.Core.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.progress

/-- info: 'Unisono.Solutions.Core.request_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.request_step

/-- info: 'Unisono.Solutions.Core.sync_zero_peers_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.sync_zero_peers_inv

/-- info: 'Unisono.Solutions.Core.star_no_peer_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.star_no_peer_messages

/-- info: 'Unisono.Solutions.Core.star_sync_snapshot_eq_sender_kalman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.star_sync_snapshot_eq_sender_kalman

/-- info: 'Unisono.Solutions.Core.star_modal_player_eq_single_mode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.star_modal_player_eq_single_mode

/-- info: 'Unisono.Solutions.Core.modal_cycle_full_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.modal_cycle_full_spec

/-- info: 'Unisono.Solutions.Core.receiver_cycle_plan_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.receiver_cycle_plan_spec

/-- info: 'Unisono.Solutions.Core.rcv_modal_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.rcv_modal_inv

/-- info: 'Unisono.Solutions.Core.withinBlock_speed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.withinBlock_speed_bound

/-- info: 'Unisono.Solutions.Core.boundary_step_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.boundary_step_safe

/-- info: 'Unisono.Solutions.Core.ideal_ntp_exchange_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.ideal_ntp_exchange_exact

/-- info: 'Unisono.Solutions.Core.ideal_kalman_and_sender_time_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.ideal_kalman_and_sender_time_exact

/-- info: 'Unisono.Solutions.Core.ideal_modal_cycle_unity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.ideal_modal_cycle_unity

/-- info: 'Unisono.Solutions.Core.ideal_zero_cost_objectives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Core.ideal_zero_cost_objectives
