/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Arrivals
public import Unisono.Device
public import Unisono.Fixed
public import Unisono.Model.Exchange
public import Unisono.Model.LineFit
public import Unisono.Model.Regulator
public import Unisono.Model.SupportLine
public import Unisono.Packet
public import Unisono.Player
public import Unisono.Presence
public import Unisono.Receiver
public import Unisono.Relation
public import Unisono.Rounds
public import Unisono.Sender

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

/-- info: 'Unisono.Player.cycle_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.cycle_spec

/-- info: 'Unisono.Player.sender_time_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.sender_time_total

/-- info: 'Unisono.Player.due_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Player.due_total

/-- info: 'Unisono.Model.Regulator.energy_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulator.energy_step

/-- info: 'Unisono.Model.Regulator.distance_from_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulator.distance_from_rest

/-- info: 'Unisono.Model.Regulator.stepWith_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulator.stepWith_shift

/-- info: 'Unisono.Model.Regulator.at_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Regulator.at_limit

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

/-- info: 'Unisono.Fixed.div_floor_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.div_floor_spec

/-- info: 'Unisono.Fixed.div_floor_wide_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Fixed.div_floor_wide_spec

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

/-- info: 'Unisono.Receiver.slide_warmup_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Receiver.slide_warmup_spec

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
