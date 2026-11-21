/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Arrivals
public import Unisono.Device
public import Unisono.Due
public import Unisono.Estimate
public import Unisono.Fixed
public import Unisono.Gains
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
public import Unisono.Solutions.FixedDelayBounded
public import Unisono.Solutions.FixedDelayMemory
public import Unisono.Spec.AtLatency
public import Unisono.Spec.Checks
public import Unisono.Spec.Run
public import Unisono.Spec.Models.Delays

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

/-- info: 'Unisono.Spec.DelayModel.example_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.DelayModel.example_holds

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

/-- info: 'Unisono.Solutions.FixedDelay.answered_question' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.answered_question

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

/-- info: 'Unisono.Solutions.FixedDelay.question_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.question_inFlight

/-- info: 'Unisono.Solutions.FixedDelay.answer_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.answer_inFlight

/-- info: 'Unisono.Solutions.FixedDelay.question_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.question_answered

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

/-- info: 'Unisono.Solutions.FixedDelay.exists_last_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exists_last_before

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
