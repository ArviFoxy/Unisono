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
public import Unisono.Model.Descent
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
public import Unisono.Solutions.Controller
public import Unisono.Solutions.Controller.Cost
public import Unisono.Solutions.Controller.Exact
public import Unisono.Solutions.Controller.HeldLevel
public import Unisono.Solutions.Controller.ExpectedCost
public import Unisono.Solutions.Controller.LateBlocks
public import Unisono.Solutions.Controller.LateRate
public import Unisono.Solutions.Controller.Limited
public import Unisono.Solutions.Controller.Pauses
public import Unisono.Solutions.Controller.Queries
public import Unisono.Solutions.Controller.Schedule
public import Unisono.Solutions.Controller.SteppedLevel
public import Unisono.Solutions.Controller.Needs
public import Unisono.Solutions.Controller.Ruled
public import Unisono.Solutions.Controller.Knots
public import Unisono.Solutions.Controller.Envelope
public import Unisono.Solutions.Controller.Timing
public import Unisono.Solutions.Controller.KnotLevel
public import Unisono.Solutions.Controller.DueSchedule
public import Unisono.Solutions.Controller.Arrived
public import Unisono.Solutions.Controller.Silent
public import Unisono.Solutions.Controller.Targets
public import Unisono.Solutions.Controller.ChosenLatency
public import Unisono.Solutions.Controller.EstimateStep
public import Unisono.Solutions.Controller.Checked
public import Unisono.Solutions.Controller.Late
public import Unisono.Solutions.Controller.BuiltLate
public import Unisono.Solutions.Controller.BuiltRoom
public import Unisono.Solutions.Controller.OrderedView
public import Unisono.Solutions.Controller.IdleView
public import Unisono.Solutions.Controller.IdleExchanges
public import Unisono.Solutions.Controller.IdleRequests
public import Unisono.Solutions.Controller.IdleEstimate
public import Unisono.Solutions.Controller.IdleKnots
public import Unisono.Solutions.Controller.DuePosition
public import Unisono.Solutions.Controller.Combined
public import Unisono.Solutions.Controller.Undelayed
public import Unisono.Solutions.Controller.Views
public import Unisono.Solutions.Core
public import Unisono.Solutions.FixedDelay.Arrivals
public import Unisono.Solutions.FixedDelay.Exact
public import Unisono.Solutions.FixedDelay.Latency
public import Unisono.Solutions.FixedDelay.Memory
public import Unisono.Solutions.FixedDelay.NoLoss
public import Unisono.Solutions.FixedDelay.Speed
public import Unisono.Solutions.FixedDelay.StarMargin
public import Unisono.Spec.AccruedLower
public import Unisono.Spec.AtLatency
public import Unisono.Spec.BlockCounts
public import Unisono.Spec.Causality
public import Unisono.Spec.CellWindows
public import Unisono.Spec.CellCount
public import Unisono.Spec.Checks
public import Unisono.Spec.EarliestArrival
public import Unisono.Spec.ExactCost
public import Unisono.Spec.ExactLatency
public import Unisono.Spec.Held
public import Unisono.Spec.Limiter
public import Unisono.Spec.Follower
public import Unisono.Spec.OwnEvents
public import Unisono.Spec.PlayedSteps
public import Unisono.Spec.FollowerSteps
public import Unisono.Spec.FollowerCost
public import Unisono.Spec.FollowerRun
public import Unisono.Spec.FollowerNear
public import Unisono.Spec.ViewOrder
public import Unisono.Spec.Limits
public import Unisono.Spec.MissingSamples
public import Unisono.Spec.OutputRate
public import Unisono.Spec.Models.Delays
public import Unisono.Spec.Models.ErgodicCells
public import Unisono.Spec.Models.ErgodicMean
public import Unisono.Spec.Models.GenerativeBlockLatency
public import Unisono.Spec.Models.GenerativeCanonical
public import Unisono.Spec.Models.GenerativeDelivery
public import Unisono.Spec.Models.GenerativeEarliest
public import Unisono.Spec.Models.GenerativeIdle
public import Unisono.Spec.Models.GenerativeLate
public import Unisono.Spec.Models.GenerativeLawOfDraw
public import Unisono.Spec.Models.GenerativeLeastLatency
public import Unisono.Spec.Models.GenerativeLinkPause
public import Unisono.Spec.Models.GenerativeNoiseless
public import Unisono.Spec.Models.GenerativePauseLaw
public import Unisono.Spec.Models.GenerativePauses
public import Unisono.Spec.Models.GenerativeRates
public import Unisono.Spec.Models.GenerativeReflection
public import Unisono.Spec.Models.GenerativeDrawLaw
public import Unisono.Spec.Models.GenerativeResample
public import Unisono.Spec.Models.GenerativeBlockSum
public import Unisono.Spec.Models.GenerativeCellStall
public import Unisono.Spec.Models.GenerativeCellMean
public import Unisono.Spec.Models.GenerativeCellPause
public import Unisono.Spec.Models.GenerativeHorizon
public import Unisono.Spec.Models.GenerativeLongRun
public import Unisono.Spec.Models.GenerativeLimit
public import Unisono.Spec.Models.GenerativeFrameBound
public import Unisono.Spec.Models.GenerativeClockMean
public import Unisono.Spec.Models.GenerativeLevelProgram
public import Unisono.Spec.Models.GenerativeSteadyBound
public import Unisono.Spec.Models.GenerativeProgress
public import Unisono.Spec.Models.GenerativeClocks
public import Unisono.Spec.Models.GaussianLaw
public import Unisono.Spec.Models.GenerativeShift
public import Unisono.Spec.Models.DyadicLimit
public import Unisono.Spec.Models.ContinuousModification
public import Unisono.Spec.Models.StationaryGaussian
public import Unisono.Spec.Models.ClockAdvance
public import Unisono.Spec.Models.ProposedWorld
public import Unisono.Spec.Models.ProposedBuild
public import Unisono.Spec.Models.ProposedExists
public import Unisono.Spec.Models.GenerativeIdlePath
public import Unisono.Spec.Models.GenerativeUndisturbed
public import Unisono.Spec.Models.GenerativeResamplePauses
public import Unisono.Spec.Models.GenerativeRoom
public import Unisono.Spec.Models.GenerativeStall
public import Unisono.Spec.Models.GenerativeStar
public import Unisono.Spec.Models.GenerativeTransfer
public import Unisono.Spec.Models.GenerativeWorld
public import Unisono.Spec.Models.PauseProcess
public import Unisono.Spec.Models.Ideal
public import Unisono.Spec.Models.IncrementLaw
public import Unisono.Spec.Models.IncrementParts
public import Unisono.Spec.Models.MeasurableDelay
public import Unisono.Spec.Models.SecondOrder
public import Unisono.Spec.Models.StochasticWorld
public import Unisono.Spec.MoreInMessages
public import Unisono.Spec.NewGround
public import Unisono.Spec.Optimality
public import Unisono.Spec.Run
public import Unisono.Spec.SameMessages
public import Unisono.Spec.ShiftedPlayback
public import Unisono.Spec.Skips
public import Unisono.Spec.Stall
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

/-- info: 'Unisono.Model.Descent.clampTo_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.clampTo_mem

/-- info: 'Unisono.Model.Descent.abs_clampTo_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.abs_clampTo_sub_le

/-- info: 'Unisono.Model.Descent.mem_of_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.mem_of_rule

/-- info: 'Unisono.Model.Descent.abs_succ_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.abs_succ_sub_le

/-- info: 'Unisono.Model.Descent.sum_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.sum_sub_le

/-- info: 'Unisono.Model.Descent.abs_needSlope_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.abs_needSlope_le

/-- info: 'Unisono.Model.Descent.needCost_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.needCost_sub_le

/-- info: 'Unisono.Model.Descent.sum_needCost_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Model.Descent.sum_needCost_sub_le

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

/-- info: 'Unisono.Spec.GenerativeWorld.pauseLaw_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pauseLaw_univ

/-- info: 'Unisono.Spec.GenerativeWorld.betaPDF_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.betaPDF_one_sub

/-- info: 'Unisono.Spec.GenerativeWorld.betaMeasure_map_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.betaMeasure_map_one_sub

/-- info: 'Unisono.Spec.GenerativeWorld.betaMeasure_compl_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.betaMeasure_compl_Ioo

/-- info: 'Unisono.Spec.GenerativeWorld.pauseLaw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pauseLaw_zero

/-- info: 'Unisono.Spec.GenerativeWorld.integral_pow_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_pow_poissonMeasure

/-- info: 'Unisono.Spec.GenerativeWorld.charFun_sumLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.charFun_sumLaw

/-- info: 'Unisono.Spec.GenerativeWorld.charFun_pauseLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.charFun_pauseLaw

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_cellSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_cellSum

/-- info: 'Unisono.Spec.GenerativeWorld.integral_prod_marks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_prod_marks

/-- info: 'Unisono.Spec.GenerativeWorld.integral_cexp_cellSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_cexp_cellSum

/-- info: 'Unisono.Spec.GenerativeWorld.markIn_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.markIn_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.markIn_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.markIn_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.cellSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellSum_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.cellSum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellSum_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_eq_sum

/-- info: 'Unisono.Spec.GenerativeWorld.markIn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.markIn_add

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_add

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_self

/-- info: 'Unisono.Spec.GenerativeWorld.pausedPath_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedPath_sub

/-- info: 'Unisono.Spec.GenerativeWorld.pausedPath_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedPath_zero

/-- info: 'Unisono.Spec.GenerativeWorld.pausedPath_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedPath_monotone

/-- info: 'Unisono.Spec.GenerativeWorld.markIn_continuousWithinAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.markIn_continuousWithinAt

/-- info: 'Unisono.Spec.GenerativeWorld.pausedPath_rightContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedPath_rightContinuous

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_markIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_markIn

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_pausedBetween' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_pausedBetween

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_pausedPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_pausedPath

/-- info: 'Unisono.Spec.GenerativeWorld.integral_prod_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_prod_cells

/-- info: 'Unisono.Spec.GenerativeWorld.sum_volume_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.sum_volume_cells

/-- info: 'Unisono.Spec.GenerativeWorld.unitLaw_pauseStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.unitLaw_pauseStart

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_stepMark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_stepMark

/-- info: 'Unisono.Spec.GenerativeWorld.cexp_stepMark_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cexp_stepMark_sub_one

/-- info: 'Unisono.Spec.GenerativeWorld.integral_cexp_stepMark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_cexp_stepMark

/-- info: 'Unisono.Spec.GenerativeWorld.integral_cexp_pausedBetween' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_cexp_pausedBetween

/-- info: 'Unisono.Spec.GenerativeWorld.hasLaw_pausedBetween' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasLaw_pausedBetween

/-- info: 'Unisono.Spec.GenerativeWorld.hasLaw_pausedPath_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasLaw_pausedPath_sub

/-- info: 'Unisono.Spec.GenerativeWorld.hasIndepIncrements_pausedPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasIndepIncrements_pausedPath

/-- info: 'Unisono.Spec.GenerativeWorld.Tame.bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Tame.bddAbove

/-- info: 'Unisono.Spec.GenerativeWorld.isBacklog_backlog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.isBacklog_backlog

/-- info: 'Unisono.Spec.GenerativeWorld.le_handledAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.le_handledAt

/-- info: 'Unisono.Spec.GenerativeWorld.handledAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.handledAt_mono

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Steady.reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Steady.reading

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Steady.deviceReading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Steady.deviceReading

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Steady.lt_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Steady.lt_arrival

/-- info: 'Unisono.Spec.GenerativeWorld.exp_mul_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.exp_mul_exp_neg

/-- info: 'Unisono.Spec.GenerativeWorld.drawWorld_builds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.drawWorld_builds

/-- info: 'Unisono.Spec.GenerativeWorld.drawWorld_constantRates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.drawWorld_constantRates

/-- info: 'Unisono.Spec.GenerativeWorld.hasSum_natCast_poisson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasSum_natCast_poisson

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_natCast_poisson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_natCast_poisson

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_cellSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_cellSum

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_cellTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_cellTotal

/-- info: 'Unisono.Spec.GenerativeWorld.cellTotal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellTotal_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.cellSum_le_cellTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellSum_le_cellTotal

/-- info: 'Unisono.Spec.GenerativeWorld.ae_nonneg_of_Iic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_nonneg_of_Iic

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_cellTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_cellTotal

/-- info: 'Unisono.Spec.GenerativeWorld.integrable_cellTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integrable_cellTotal

/-- info: 'Unisono.Spec.GenerativeWorld.integral_cellTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_cellTotal

/-- info: 'Unisono.Spec.GenerativeWorld.markIn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.markIn_le

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_neg_le

/-- info: 'Unisono.Spec.GenerativeWorld.ae_tame_pausedPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_tame_pausedPath

/-- info: 'Unisono.Spec.GenerativeWorld.measurableSet_tame_pausedPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurableSet_tame_pausedPath

/-- info: 'Unisono.Spec.GenerativeWorld.tamePath_of_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tamePath_of_tame

/-- info: 'Unisono.Spec.GenerativeWorld.tamePath_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tamePath_monotone

/-- info: 'Unisono.Spec.GenerativeWorld.tamePath_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tamePath_zero

/-- info: 'Unisono.Spec.GenerativeWorld.tamePath_rightContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tamePath_rightContinuous

/-- info: 'Unisono.Spec.GenerativeWorld.tamePath_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tamePath_tame

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_tamePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_tamePath

/-- info: 'Unisono.Spec.GenerativeWorld.tamePath_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tamePath_ae_eq

/-- info: 'Unisono.Spec.GenerativeWorld.iIndepFun_of_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.iIndepFun_of_measurePreserving

/-- info: 'Unisono.Spec.GenerativeWorld.hasLaw_tamePath_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasLaw_tamePath_sub

/-- info: 'Unisono.Spec.GenerativeWorld.hasIndepIncrements_tamePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasIndepIncrements_tamePath

/-- info: 'Unisono.Spec.GenerativeWorld.Member.Noiseless.steadyClocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Member.Noiseless.steadyClocks

/-- info: 'Unisono.Spec.GenerativeWorld.Member.Noiseless.steadyHosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Member.Noiseless.steadyHosts

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_constantRates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_constantRates

/-- info: 'Unisono.Spec.GenerativeWorld.steadyDraw_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyDraw_steady

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_steadyMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_steadyMap

/-- info: 'Unisono.Spec.GenerativeWorld.steadyDraw_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyDraw_component

/-- info: 'Unisono.Spec.GenerativeWorld.steadyDraw_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyDraw_prior

/-- info: 'Unisono.Spec.GenerativeWorld.steadyWorld_builds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyWorld_builds

/-- info: 'Unisono.Spec.GenerativeWorld.exists_holds_of_steadyClocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.exists_holds_of_steadyClocks

/-- info: 'Unisono.Spec.GenerativeWorld.exists_holds_with_pauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.exists_holds_with_pauses

/-- info: 'Unisono.Spec.abs_birkhoffAverage_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.abs_birkhoffAverage_apply_sub_le

/-- info: 'Unisono.Spec.frequently_lt_of_abs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.frequently_lt_of_abs_sub_le

/-- info: 'Unisono.Spec.preimage_frequentlyAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.preimage_frequentlyAbove

/-- info: 'Unisono.Spec.measurableSet_frequentlyAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurableSet_frequentlyAbove

/-- info: 'Unisono.Spec.iterate_mem_iff_of_preimage_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.iterate_mem_iff_of_preimage_eq

/-- info: 'Unisono.Spec.birkhoffSum_indicator_of_preimage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.birkhoffSum_indicator_of_preimage_eq

/-- info: 'Unisono.Spec.measure_frequentlyAbove_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measure_frequentlyAbove_eq_zero

/-- info: 'Unisono.Spec.ae_eventually_birkhoffAverage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ae_eventually_birkhoffAverage_le

/-- info: 'Unisono.Spec.tendsto_birkhoffAverage_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.tendsto_birkhoffAverage_ae

/-- info: 'Unisono.Spec.frequently_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.frequently_succ_iff

/-- info: 'Unisono.Spec.ae_frequently_mem_of_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ae_frequently_mem_of_ergodic

/-- info: 'Unisono.Spec.preErgodic_of_mixing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.preErgodic_of_mixing

/-- info: 'Unisono.Spec.measurable_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_shiftCells

/-- info: 'Unisono.Spec.iterate_shiftCells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.iterate_shiftCells

/-- info: 'Unisono.Spec.measurePreserving_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurePreserving_shiftCells

/-- info: 'Unisono.Spec.measure_inter_preimage_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measure_inter_preimage_shiftCells

/-- info: 'Unisono.Spec.ergodic_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ergodic_shiftCells

/-- info: 'Unisono.Spec.measure_inter_of_disjoint_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measure_inter_of_disjoint_cells

/-- info: 'Unisono.Spec.succ_mul_birkhoffAverage_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.succ_mul_birkhoffAverage_succ

/-- info: 'Unisono.Spec.birkhoffAverage_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.birkhoffAverage_nonneg

/-- info: 'Unisono.Spec.preimage_frequentlyAbove_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.preimage_frequentlyAbove_of_nonneg

/-- info: 'Unisono.Spec.frequentlyAbove_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.frequentlyAbove_antitone

/-- info: 'Unisono.Spec.mul_measureReal_le_setIntegral_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.mul_measureReal_le_setIntegral_of_subset

/-- info: 'Unisono.Spec.limsup_le_of_notMem_frequentlyAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limsup_le_of_notMem_frequentlyAbove

/-- info: 'Unisono.Spec.lintegral_limsup_birkhoffAverage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_limsup_birkhoffAverage_le

/-- info: 'Unisono.Spec.lintegral_limsup_average_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_limsup_average_le

/-- info: 'Unisono.Spec.exists_rat_seq_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_rat_seq_gt

/-- info: 'Unisono.Spec.aemeasurable_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.aemeasurable_path

/-- info: 'Unisono.Spec.sortedTimes_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sortedTimes_monotone

/-- info: 'Unisono.Spec.exists_sortedTimes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_sortedTimes_eq

/-- info: 'Unisono.Spec.timeIndex_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.timeIndex_lt

/-- info: 'Unisono.Spec.sortedTimes_timeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sortedTimes_timeIndex

/-- info: 'Unisono.Spec.measurable_valuesOfIncrements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_valuesOfIncrements

/-- info: 'Unisono.Spec.sum_increments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_increments

/-- info: 'Unisono.Spec.HasIncrementLaws.aemeasurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.HasIncrementLaws.aemeasurable

/-- info: 'Unisono.Spec.HasIncrementLaws.map_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.HasIncrementLaws.map_restrict

/-- info: 'Unisono.Spec.HasIncrementLaws.map_path_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.HasIncrementLaws.map_path_eq

/-- info: 'Unisono.Spec.map_paths_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.map_paths_eq

/-- info: 'Unisono.Spec.map_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.map_row

/-- info: 'Unisono.Spec.map_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.map_rows

/-- info: 'Unisono.Spec.iIndepFun_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.iIndepFun_rows

/-- info: 'Unisono.Spec.GenerativeWorld.Member.pauseRate_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Member.pauseRate_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.Member.pauseLength_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Member.pauseLength_pos

/-- info: 'Unisono.Spec.GenerativeWorld.Member.pauseLength_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Member.pauseLength_mean

/-- info: 'Unisono.Spec.GenerativeWorld.Member.pauseLoad_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Member.pauseLoad_lt_one

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.hasIncrementLaws_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.hasIncrementLaws_paused

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.aemeasurable_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.aemeasurable_paused

/-- info: 'Unisono.Spec.GenerativeWorld.pauseComponent_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pauseComponent_injective

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.iIndepFun_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.iIndepFun_paused

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_cellPaused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_cellPaused

/-- info: 'Unisono.Spec.GenerativeWorld.measurePreserving_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurePreserving_row

/-- info: 'Unisono.Spec.GenerativeWorld.hasIncrementLaws_cellPaused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasIncrementLaws_cellPaused

/-- info: 'Unisono.Spec.GenerativeWorld.iIndepFun_cellPaused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.iIndepFun_cellPaused

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_paused

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_paused_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_paused_mem

/-- info: 'Unisono.Spec.GenerativeWorld.IdleAt.sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IdleAt.sub_le

/-- info: 'Unisono.Spec.GenerativeWorld.IdleOn.isBacklog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IdleOn.isBacklog

/-- info: 'Unisono.Spec.GenerativeWorld.measurableSet_idleOften' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurableSet_idleOften

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_clearFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_clearFrom

/-- info: 'Unisono.Spec.GenerativeWorld.cellSum_of_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellSum_of_empty

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_eq_zero_of_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_eq_zero_of_empty

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_clearFrom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_clearFrom_le

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_clearFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_clearFrom_eq

/-- info: 'Unisono.Spec.GenerativeWorld.pausedBetween_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedBetween_shiftCells

/-- info: 'Unisono.Spec.GenerativeWorld.mem_emptyUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.mem_emptyUpTo

/-- info: 'Unisono.Spec.GenerativeWorld.measurableSet_boundedBefore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurableSet_boundedBefore

/-- info: 'Unisono.Spec.GenerativeWorld.measurableSet_emptyUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurableSet_emptyUpTo

/-- info: 'Unisono.Spec.GenerativeWorld.measure_emptyUpTo_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measure_emptyUpTo_ne_zero

/-- info: 'Unisono.Spec.GenerativeWorld.idleOn_of_bounded_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.idleOn_of_bounded_empty

/-- info: 'Unisono.Spec.GenerativeWorld.cellPaused_shiftCells_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellPaused_shiftCells_sub

/-- info: 'Unisono.Spec.GenerativeWorld.idleOn_of_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.idleOn_of_shiftCells

/-- info: 'Unisono.Spec.GenerativeWorld.exists_boundedBefore_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.exists_boundedBefore_ne_zero

/-- info: 'Unisono.Spec.GenerativeWorld.ae_cellPaused_mem_idleOften' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_cellPaused_mem_idleOften

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_idle

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_ratAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_ratAfter

/-- info: 'Unisono.Spec.GenerativeWorld.lt_ratAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lt_ratAfter

/-- info: 'Unisono.Spec.GenerativeWorld.ratAfter_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ratAfter_le

/-- info: 'Unisono.Spec.GenerativeWorld.tendsto_ratAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.tendsto_ratAfter

/-- info: 'Unisono.Spec.GenerativeWorld.valueAfter_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.valueAfter_eq

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_valueAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_valueAfter

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_backlogM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_backlogM

/-- info: 'Unisono.Spec.GenerativeWorld.backlogM_eq_iSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.backlogM_eq_iSup

/-- info: 'Unisono.Spec.GenerativeWorld.backlogM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.backlogM_eq

/-- info: 'Unisono.Spec.GenerativeWorld.backlogM_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.backlogM_shift

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_backlogM_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_backlogM_comp

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_arrivalM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_arrivalM

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_eq_arrivalM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_eq_arrivalM

/-- info: 'Unisono.Spec.GenerativeWorld.arrivalM_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.arrivalM_shift

/-- info: 'Unisono.Spec.GenerativeWorld.pausedPath_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pausedPath_shiftCells

/-- info: 'Unisono.Spec.GenerativeWorld.cellPaused_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellPaused_monotone

/-- info: 'Unisono.Spec.GenerativeWorld.cellPaused_rightContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellPaused_rightContinuous

/-- info: 'Unisono.Spec.GenerativeWorld.cellPaused_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellPaused_shiftCells

/-- info: 'Unisono.Spec.GenerativeWorld.arrivalM_cellPaused_shiftCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.arrivalM_cellPaused_shiftCells

/-- info: 'Unisono.Spec.GenerativeWorld.ae_tendsto_lateFrequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_tendsto_lateFrequency

/-- info: 'Unisono.Spec.GenerativeWorld.measurableSet_late' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurableSet_late

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_lateFraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_lateFraction

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_paused_eq_pathLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_paused_eq_pathLaw

/-- info: 'Unisono.Spec.GenerativeWorld.map_cellPaused_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.map_cellPaused_shift

/-- info: 'Unisono.Spec.GenerativeWorld.measureReal_late_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measureReal_late_cells

/-- info: 'Unisono.Spec.GenerativeWorld.ae_tendsto_lateFraction_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_tendsto_lateFraction_cells

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_tendsto_lateFraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_tendsto_lateFraction

/-- info: 'Unisono.Spec.GenerativeWorld.map_cellPaused_eq_pathLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.map_cellPaused_eq_pathLaw

/-- info: 'Unisono.Spec.GenerativeWorld.ae_mem_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_mem_of_indepFun

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_lateFraction_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_lateFraction_prod

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_lateProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_lateProbability

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_lateFraction_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_lateFraction_indep

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_scalarCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_scalarCast

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_pauseCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_pauseCast

/-- info: 'Unisono.Spec.GenerativeWorld.scalarComponent_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.scalarComponent_injective

/-- info: 'Unisono.Spec.GenerativeWorld.scalarComponent_ne_pause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.scalarComponent_ne_pause

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.aemeasurable_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.aemeasurable_scalar

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.indepFun_scalars_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.indepFun_scalars_paused

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.aemeasurable_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.aemeasurable_scalars

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_lateFraction_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_lateFraction_scalars

/-- info: 'Unisono.Spec.GenerativeWorld.abs_lastNeeded_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.abs_lastNeeded_sub_lt

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.mem_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.mem_block

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.block_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.block_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_lt_of_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_lt_of_plays

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.arrival_lt_of_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.arrival_lt_of_plays

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.leastLatency_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.leastLatency_lt

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.lt_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.lt_latency

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.block_le_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.block_le_latency

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.exists_le_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.exists_le_handed

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.room_le_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.room_le_latency

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.le_sum_min_add_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.le_sum_min_add_loss

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.le_sum_add_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.le_sum_add_loss

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.stall_le_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.stall_le_room

/-- info: 'Unisono.Spec.clampTime_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clampTime_of_le

/-- info: 'Unisono.Spec.clampTime_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clampTime_of_ge

/-- info: 'Unisono.Spec.clampTime_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clampTime_of_mem

/-- info: 'Unisono.Spec.clampTime_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clampTime_monotone

/-- info: 'Unisono.Spec.le_clampTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_clampTime

/-- info: 'Unisono.Spec.clampTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clampTime_le

/-- info: 'Unisono.Spec.continuous_clampTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuous_clampTime

/-- info: 'Unisono.Spec.pathOutside_add_pathWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathOutside_add_pathWithin

/-- info: 'Unisono.Spec.pathWithin_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_of_le

/-- info: 'Unisono.Spec.pathWithin_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_of_ge

/-- info: 'Unisono.Spec.pathWithin_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_of_mem

/-- info: 'Unisono.Spec.pathOutside_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathOutside_of_le

/-- info: 'Unisono.Spec.pathOutside_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathOutside_eq

/-- info: 'Unisono.Spec.pathWithin_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_monotone

/-- info: 'Unisono.Spec.pathOutside_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathOutside_monotone

/-- info: 'Unisono.Spec.pathWithin_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_nonneg

/-- info: 'Unisono.Spec.pathWithin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_le

/-- info: 'Unisono.Spec.pathWithin_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_eq_zero

/-- info: 'Unisono.Spec.pathOutside_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathOutside_sub_le

/-- info: 'Unisono.Spec.pathWithin_rightContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathWithin_rightContinuous

/-- info: 'Unisono.Spec.pathOutside_rightContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pathOutside_rightContinuous

/-- info: 'Unisono.Spec.measurable_pathWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_pathWithin

/-- info: 'Unisono.Spec.measurable_pathOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_pathOutside

/-- info: 'Unisono.Spec.timeIndex_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.timeIndex_le

/-- info: 'Unisono.Spec.measurable_extendZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_extendZero

/-- info: 'Unisono.Spec.extendZero_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.extendZero_restrict

/-- info: 'Unisono.Spec.indepFun_restrict_pathWithin_pathOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.indepFun_restrict_pathWithin_pathOutside

/-- info: 'Unisono.Spec.indepFun_pathWithin_pathOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.indepFun_pathWithin_pathOutside

/-- info: 'Unisono.Spec.map_prod_comp_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.map_prod_comp_eq_prod

/-- info: 'Unisono.Spec.indepFun_comp_prodMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.indepFun_comp_prodMk

/-- info: 'Unisono.Spec.GenerativeWorld.map_comp_of_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.map_comp_of_map_eq

/-- info: 'Unisono.Spec.GenerativeWorld.iIndepFun_comp_of_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.iIndepFun_comp_of_map_eq

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_tuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_tuple

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_split

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_offset

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_logRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_logRate

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_wander' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_wander

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_linkPaused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_linkPaused

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_hostPaused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_hostPaused

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_deviceLogRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_deviceLogRate

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_deviceWander' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_deviceWander

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw_reportError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw_reportError

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_draw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_draw

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_component

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.aemeasurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.aemeasurable

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.of_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.of_map_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.withLink_linkPaused_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.withLink_linkPaused_self

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.withLink_linkPaused_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.withLink_linkPaused_of_ne

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.withLink_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.withLink_self

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.withLink_withLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.withLink_withLink

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_withLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_withLink

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.indepFun_withLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.indepFun_withLink

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.linkOutside_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.linkOutside_self

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.linkOutside_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.linkOutside_of_ne

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.linkOutside_addLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.linkOutside_addLink

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.addLink_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.addLink_zero

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.sameExcept_linkOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.sameExcept_linkOutside

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_linkOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_linkOutside

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_addLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_addLink

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.indepFun_linkOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.indepFun_linkOutside

/-- info: 'Unisono.Spec.GenerativeWorld.resample_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.resample_self

/-- info: 'Unisono.Spec.GenerativeWorld.resample_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.resample_of_eq

/-- info: 'Unisono.Spec.GenerativeWorld.resample_linkPaused_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.resample_linkPaused_self

/-- info: 'Unisono.Spec.GenerativeWorld.resample_linkPaused_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.resample_linkPaused_of_ne

/-- info: 'Unisono.Spec.GenerativeWorld.aemeasurable_resample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.aemeasurable_resample

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_resample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_resample

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.prior_resample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.prior_resample

/-- info: 'Unisono.Spec.GenerativeWorld.isBacklog_of_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.isBacklog_of_bddAbove

/-- info: 'Unisono.Spec.GenerativeWorld.IsBacklog.bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IsBacklog.bddAbove

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.bddAbove_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.bddAbove_link

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.bddAbove_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.bddAbove_host

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.exists_of_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.exists_of_paused

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.exists_linkOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.exists_linkOutside

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.exists_resample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.exists_resample

/-- info: 'Unisono.Spec.GenerativeWorld.pauseLaw_singleton_zero_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pauseLaw_singleton_zero_pos

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_linkOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_linkOutside

/-- info: 'Unisono.Spec.GenerativeWorld.ae_plays_linkOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_plays_linkOutside

/-- info: 'Unisono.Spec.GenerativeWorld.ae_plays_linkOutside_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ae_plays_linkOutside_of

/-- info: 'Unisono.Spec.GenerativeWorld.ofReal_mul_min_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ofReal_mul_min_le

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.room_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.room_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.sum_blocks_le_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.sum_blocks_le_latency

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.capture_lt_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.capture_lt_out

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_withLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_withLinks

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.indepFun_withLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.indepFun_withLinks

/-- info: 'Unisono.Spec.GenerativeWorld.aemeasurable_resampleLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.aemeasurable_resampleLinks

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_resampleLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_resampleLinks

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.prior_resampleLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.prior_resampleLinks

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.exists_resampleLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.exists_resampleLinks

/-- info: 'Unisono.Spec.GenerativeWorld.expectedCost_resampleLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.expectedCost_resampleLinks

/-- info: 'Unisono.Spec.le_asked_firstFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_asked_firstFrom

/-- info: 'Unisono.Spec.asked_lt_of_lt_firstFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.asked_lt_of_lt_firstFrom

/-- info: 'Unisono.Spec.windowCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.windowCount_le

/-- info: 'Unisono.Spec.asked_le_of_windowCount_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.asked_le_of_windowCount_pos

/-- info: 'Unisono.Spec.windowCount_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.windowCount_mono

/-- info: 'Unisono.Spec.le_min_of_windowCount_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_min_of_windowCount_pos

/-- info: 'Unisono.Spec.disjoint_cellSamples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.disjoint_cellSamples

/-- info: 'Unisono.Spec.sum_cellSamples_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_cellSamples_le

/-- info: 'Unisono.Spec.card_mul_le_of_firstFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.card_mul_le_of_firstFrom

/-- info: 'Unisono.Spec.le_windowCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_windowCount

/-- info: 'Unisono.Spec.mem_countedCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.mem_countedCells

/-- info: 'Unisono.Spec.card_countedCells_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.card_countedCells_le

/-- info: 'Unisono.Spec.le_card_countedCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_card_countedCells

/-- info: 'Unisono.Spec.mul_le_card_countedCells_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.mul_le_card_countedCells_mul

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.exists_le_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.exists_le_asked

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.cell_stall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.cell_stall_le

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_prodMk_of_indepFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_prodMk_of_indepFun

/-- info: 'Unisono.Spec.GenerativeWorld.pauseLaw_ge_dirac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pauseLaw_ge_dirac

/-- info: 'Unisono.Spec.GenerativeWorld.pauseLaw_ge_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.pauseLaw_ge_smul

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_pauseLaw_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_pauseLaw_ge

/-- info: 'Unisono.Spec.GenerativeWorld.eq_describedPlays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.eq_describedPlays

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_getD_lastPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_getD_lastPlayed

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.lintegral_cell_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.lintegral_cell_ge

/-- info: 'Unisono.Spec.GenerativeWorld.blockFrom_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.blockFrom_congr

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.linkOutside_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.linkOutside_eq_self

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.cell_mean_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.cell_mean_ge

/-- info: 'Unisono.Spec.sum_ite_cellSamples_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_ite_cellSamples_le

/-- info: 'Unisono.Spec.sum_share_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_share_le

/-- info: 'Unisono.Spec.sum_lintegral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_lintegral_le

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.sum_cellValue_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.sum_cellValue_le

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.cellsCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.cellsCost_le

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.sum_cells_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.sum_cells_le

/-- info: 'Unisono.Spec.World.accrued_ge_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.accrued_ge_of_blocks

/-- info: 'Unisono.Spec.World.sum_le_captureDeficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sum_le_captureDeficit

/-- info: 'Unisono.Spec.World.sum_le_accrued_add_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sum_le_accrued_add_loss

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.lintegral_clear_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.lintegral_clear_ge

/-- info: 'Unisono.Spec.limsup_lintegral_le_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limsup_lintegral_le_of_bounded

/-- info: 'Unisono.Spec.limsup_le_longRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limsup_le_longRun

/-- info: 'Unisono.Spec.limsup_le_lintegral_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limsup_le_lintegral_cost

/-- info: 'Unisono.Spec.le_limsup_sub_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_limsup_sub_div

/-- info: 'Unisono.Spec.GenerativeWorld.cellFloor_le_cellValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellFloor_le_cellValue

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.limsup_cells_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.limsup_cells_le_cost

/-- info: 'Unisono.Spec.GenerativeWorld.cellsCost_le_cellsCap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.cellsCost_le_cellsCap

/-- info: 'Unisono.Spec.GenerativeWorld.le_fixedClockBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.le_fixedClockBound

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.value_le_lintegral_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.value_le_lintegral_cost

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_fixedClockBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_fixedClockBound_le

/-- info: 'Unisono.Spec.GenerativeWorld.levelFloor_le_levelValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.levelFloor_le_levelValue

/-- info: 'Unisono.Spec.GenerativeWorld.levelValue_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.levelValue_ne_top

/-- info: 'Unisono.Spec.GenerativeWorld.mul_levelLatency_le_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.mul_levelLatency_le_cell

/-- info: 'Unisono.Spec.GenerativeWorld.mul_levelFloor_le_cellFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.mul_levelFloor_le_cellFloor

/-- info: 'Unisono.Spec.GenerativeWorld.mul_levelValue_le_cellValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.mul_levelValue_le_cellValue

/-- info: 'Unisono.Spec.GenerativeWorld.capturePeriodOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.capturePeriodOf_pos

/-- info: 'Unisono.Spec.GenerativeWorld.outputPeriodOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.outputPeriodOf_pos

/-- info: 'Unisono.Spec.GenerativeWorld.leadOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.leadOf_pos

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.capture_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.capture_succ_sub

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.out_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.out_eq

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.asked_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.asked_eq

/-- info: 'Unisono.Spec.GenerativeWorld.blocksBefore_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.blocksBefore_spec

/-- info: 'Unisono.Spec.GenerativeWorld.steadyHorizon_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyHorizon_pos

/-- info: 'Unisono.Spec.GenerativeWorld.out_zero_lt_steadyHorizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.out_zero_lt_steadyHorizon

/-- info: 'Unisono.Spec.GenerativeWorld.steadyChoices_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyChoices_valid

/-- info: 'Unisono.Spec.GenerativeWorld.steadyRate_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.steadyRate_ne_top

/-- info: 'Unisono.Spec.GenerativeWorld.mul_steadyRate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.mul_steadyRate_le

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.steadyBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.steadyBound_le

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_steadyBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_steadyBound_le

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.handed_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.handed_unbounded

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.asked_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.asked_unbounded

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.rate_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.rate_pos

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.deviceRate_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.deviceRate_pos

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.continuous_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.continuous_rate

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.continuous_deviceRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.continuous_deviceRate

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.reading_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.reading_sub

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.deviceReading_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.deviceReading_sub

/-- info: 'Unisono.Spec.GenerativeWorld.integral_mem_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.integral_mem_of_band

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.reading_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.reading_sub_mem

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.deviceReading_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.deviceReading_sub_mem

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.capture_succ_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.capture_succ_sub_mem

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.out_succ_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.out_succ_sub_mem

/-- info: 'Unisono.Spec.integral_variance_linear_of_isGaussianProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.integral_variance_linear_of_isGaussianProcess

/-- info: 'Unisono.Spec.map_eq_of_isGaussianProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.map_eq_of_isGaussianProcess

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_path_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_path_shift

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_path_shift_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_path_shift_sub

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_component_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_component_shift

/-- info: 'Unisono.Spec.GenerativeWorld.map_shift_of_isGaussianProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.map_shift_of_isGaussianProcess

/-- info: 'Unisono.Spec.GenerativeWorld.map_shift_of_hasIncrementLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.map_shift_of_hasIncrementLaws

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_component_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_component_shift

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_components_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_components_shift

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_shiftComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_shiftComponents

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.lintegral_limsup_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.lintegral_limsup_shift

/-- info: 'Unisono.Spec.dyadicFloor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.dyadicFloor_le

/-- info: 'Unisono.Spec.lt_dyadicFloor_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lt_dyadicFloor_add

/-- info: 'Unisono.Spec.abs_dyadicFloor_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.abs_dyadicFloor_sub_le

/-- info: 'Unisono.Spec.floor_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.floor_succ_eq

/-- info: 'Unisono.Spec.floor_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.floor_mem_range

/-- info: 'Unisono.Spec.StepsWithin.abs_succ_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StepsWithin.abs_succ_sub_le

/-- info: 'Unisono.Spec.StepsWithin.abs_sub_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StepsWithin.abs_sub_le_of_near

/-- info: 'Unisono.Spec.StepsWithin.tendsto_dyadicLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StepsWithin.tendsto_dyadicLimit

/-- info: 'Unisono.Spec.StepsWithin.abs_sub_dyadicLimit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StepsWithin.abs_sub_dyadicLimit_le

/-- info: 'Unisono.Spec.StepsWithin.abs_dyadicLimit_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StepsWithin.abs_dyadicLimit_sub_le

/-- info: 'Unisono.Spec.StepsWithin.continuousOn_dyadicLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.StepsWithin.continuousOn_dyadicLimit

/-- info: 'Unisono.Spec.abs_le_add_pow_four_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.abs_le_add_pow_four_div

/-- info: 'Unisono.Spec.stepPowers_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepPowers_nonneg

/-- info: 'Unisono.Spec.stepBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepBound_nonneg

/-- info: 'Unisono.Spec.stepsWithin_stepBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepsWithin_stepBound

/-- info: 'Unisono.Spec.measurable_stepPowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_stepPowers

/-- info: 'Unisono.Spec.measurable_stepBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_stepBound

/-- info: 'Unisono.Spec.summable_iff_tsum_ofReal_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.summable_iff_tsum_ofReal_ne_top

/-- info: 'Unisono.Spec.measurableSet_summableSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurableSet_summableSteps

/-- info: 'Unisono.Spec.exists_nat_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_nat_abs_lt

/-- info: 'Unisono.Spec.continuous_continuousModification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuous_continuousModification

/-- info: 'Unisono.Spec.tendsto_continuousModification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.tendsto_continuousModification

/-- info: 'Unisono.Spec.measurable_continuousModification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_continuousModification

/-- info: 'Unisono.Spec.ae_mem_summableSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ae_mem_summableSteps

/-- info: 'Unisono.Spec.continuousModification_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuousModification_ae_eq

/-- info: 'Unisono.Spec.pow_four_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.pow_four_le_exp

/-- info: 'Unisono.Spec.exp_half_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exp_half_le_two

/-- info: 'Unisono.Spec.lintegral_pow_four_gaussianReal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_pow_four_gaussianReal_le

/-- info: 'Unisono.Spec.lintegral_pow_four_le_of_hasGaussianLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_pow_four_le_of_hasGaussianLaw

/-- info: 'Unisono.Spec.covariance_congr_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.covariance_congr_ae

/-- info: 'Unisono.Spec.exists_continuous_of_isGaussianProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_continuous_of_isGaussianProcess

/-- info: 'Unisono.Spec.exists_isPreBrownianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_isPreBrownianReal

/-- info: 'Unisono.Spec.exp_mul_exp_mul_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exp_mul_exp_mul_min

/-- info: 'Unisono.Spec.scaledBrownian_isGaussianProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.scaledBrownian_isGaussianProcess

/-- info: 'Unisono.Spec.integral_scaledBrownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.integral_scaledBrownian

/-- info: 'Unisono.Spec.covariance_scaledBrownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.covariance_scaledBrownian

/-- info: 'Unisono.Spec.exists_stationary_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_stationary_gaussian

/-- info: 'Unisono.Spec.stationaryLaw_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stationaryLaw_of_pos

/-- info: 'Unisono.Spec.stationaryPath_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stationaryPath_of_pos

/-- info: 'Unisono.Spec.measurable_stationaryPath_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_stationaryPath_apply

/-- info: 'Unisono.Spec.measurable_stationaryPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_stationaryPath

/-- info: 'Unisono.Spec.continuous_stationaryPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuous_stationaryPath

/-- info: 'Unisono.Spec.stationaryPath_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stationaryPath_eq

/-- info: 'Unisono.Spec.isGaussianProcess_stationaryPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.isGaussianProcess_stationaryPath

/-- info: 'Unisono.Spec.integral_stationaryPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.integral_stationaryPath

/-- info: 'Unisono.Spec.covariance_stationaryPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.covariance_stationaryPath

/-- info: 'Unisono.Spec.lintegral_abs_stationaryPath_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_abs_stationaryPath_le

/-- info: 'Unisono.Spec.isGaussianProcess_comp_hasLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.isGaussianProcess_comp_hasLaw

/-- info: 'Unisono.Spec.isGaussianProcess_stationaryPath_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.isGaussianProcess_stationaryPath_comp

/-- info: 'Unisono.Spec.integral_stationaryPath_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.integral_stationaryPath_comp

/-- info: 'Unisono.Spec.covariance_stationaryPath_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.covariance_stationaryPath_comp

/-- info: 'Unisono.Spec.lintegral_abs_stationaryPath_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_abs_stationaryPath_comp_le

/-- info: 'Unisono.Spec.clockAdvance_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvance_zero

/-- info: 'Unisono.Spec.clockAdvance_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvance_sub

/-- info: 'Unisono.Spec.clockAdvance_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvance_strictMono

/-- info: 'Unisono.Spec.continuous_clockAdvance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuous_clockAdvance

/-- info: 'Unisono.Spec.clockAdvance_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvance_surjective

/-- info: 'Unisono.Spec.clockAdvance_clockAdvanceTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvance_clockAdvanceTime

/-- info: 'Unisono.Spec.clockAdvanceTime_clockAdvance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvanceTime_clockAdvance

/-- info: 'Unisono.Spec.clockAdvanceTime_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvanceTime_strictMono

/-- info: 'Unisono.Spec.le_integral_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_integral_exp

/-- info: 'Unisono.Spec.measure_integral_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measure_integral_exp_le

/-- info: 'Unisono.Spec.ae_tendsto_integral_exp_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ae_tendsto_integral_exp_atTop

/-- info: 'Unisono.Spec.ae_tendsto_integral_exp_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ae_tendsto_integral_exp_atBot

/-- info: 'Unisono.Spec.clockAdvance_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.clockAdvance_const_add

/-- info: 'Unisono.Spec.ae_tendsto_clockAdvance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ae_tendsto_clockAdvance

/-- info: 'Unisono.Spec.lintegral_abs_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lintegral_abs_sum_le

/-- info: 'Unisono.Spec.ProposedWorld.Draw.reading_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.reading_eq

/-- info: 'Unisono.Spec.ProposedWorld.Draw.deviceReading_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.deviceReading_eq

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.clock_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.clock_continuous

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.device_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.device_continuous

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.clock_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.clock_surjective

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.device_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.device_surjective

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.reading_timeOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.reading_timeOf

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.reading_deviceTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.reading_deviceTime

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.deviceTime_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.deviceTime_zero

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.deviceTime_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.deviceTime_strict

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.hostBacklog_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.hostBacklog_nonneg

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.linkBacklog_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.linkBacklog_nonneg

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.lt_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.lt_reaches

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.reaches_le_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.reaches_le_observed

/-- info: 'Unisono.Spec.ProposedWorld.Draw.Regular.reach_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Draw.Regular.reach_mem

/-- info: 'Unisono.Spec.ProposedWorld.drawWorld_builds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.drawWorld_builds

/-- info: 'Unisono.Spec.ProposedWorld.IsEpisodePath.comp_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.IsEpisodePath.comp_ae_eq

/-- info: 'Unisono.Spec.ProposedWorld.Prior.comp_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.Prior.comp_ae_eq

/-- info: 'Unisono.Spec.ProposedWorld.dropLaw_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.dropLaw_true

/-- info: 'Unisono.Spec.ProposedWorld.dropLaw_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.dropLaw_prob

/-- info: 'Unisono.Spec.ProposedWorld.measurable_partMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.measurable_partMap

/-- info: 'Unisono.Spec.ProposedWorld.canonicalDraw_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.canonicalDraw_part

/-- info: 'Unisono.Spec.ProposedWorld.isEpisodePath_tamePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.isEpisodePath_tamePath

/-- info: 'Unisono.Spec.ProposedWorld.isEpisodePath_pausedPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.isEpisodePath_pausedPath

/-- info: 'Unisono.Spec.ProposedWorld.canonicalDraw_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.canonicalDraw_prior

/-- info: 'Unisono.Spec.ProposedWorld.ae_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.ae_regular

/-- info: 'Unisono.Spec.ProposedWorld.exists_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ProposedWorld.exists_holds

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_eq_of_pathIdle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_eq_of_pathIdle

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_le_of_pathIdle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_le_of_pathIdle

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.le_of_lt_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.le_of_lt_arrival

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.handed_of_idleOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.handed_of_idleOn

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.asked_of_idleOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.asked_of_idleOn

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_of_captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_of_captured

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.block_of_lt_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.block_of_lt_arrival

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.regular

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Regular.leastDelay_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Regular.leastDelay_pos

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Regular.leastDelay_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Regular.leastDelay_add

/-- info: 'Unisono.Spec.GenerativeWorld.RateBands.driftDown_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.RateBands.driftDown_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.RateBands.driftUp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.RateBands.driftUp_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.RateBands.ratioWidth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.RateBands.ratioWidth_nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.IdleOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IdleOn.mono

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.PathIdle.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.PathIdle.mono

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Undisturbed.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Undisturbed.mono

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Undisturbed.sender_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Undisturbed.sender_sub

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Undisturbed.host_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Undisturbed.host_sub

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Undisturbed.capture_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Undisturbed.capture_sub

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.Undisturbed.output_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.Undisturbed.output_sub

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.le_of_plays_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.le_of_plays_before

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.stall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.stall_le

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.stall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.stall_le

/-- info: 'Unisono.Spec.GenerativeWorld.backlog_eq_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.backlog_eq_of_agree

/-- info: 'Unisono.Spec.GenerativeWorld.arrival_of_sameExceptLinkFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.arrival_of_sameExceptLinkFrom

/-- info: 'Unisono.Spec.GenerativeWorld.IsBacklog.increment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IsBacklog.increment_le

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_ge_of_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_ge_of_paused

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.stall_le_of_paused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.stall_le_of_paused

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.same_devices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.same_devices

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.deliversSameBefore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.deliversSameBefore

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.plays_eq_of_sameExcept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.plays_eq_of_sameExcept

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.lastPlayed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.lastPlayed_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.stall_le_of_sameExcept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.stall_le_of_sameExcept

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.ofParts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.ofParts_eq

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_ofParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_ofParts

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_scalars_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_scalars_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.map_parts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.map_parts_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.lintegral_draw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.lintegral_draw_eq

/-- info: 'Unisono.Spec.GenerativeWorld.expectedCost_eq_of_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.expectedCost_eq_of_steady

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

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.linkPaused_ae_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.linkPaused_ae_const

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.hostPaused_ae_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.hostPaused_ae_const

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.deviceLogRate_ae_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.deviceLogRate_ae_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.deviceWander_ae_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.deviceWander_ae_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.reportError_ae_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.reportError_ae_eq_zero

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.deviceReading_noiseless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.deviceReading_noiseless

/-- info: 'Unisono.Spec.GenerativeWorld.isBacklog_zero_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.isBacklog_zero_of_const

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.exists_request_le_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.exists_request_le_asked

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.handed_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.handed_of_const

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.asked_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.asked_of_const

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

/-- info: 'Unisono.Spec.lastPlayed_succ_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lastPlayed_succ_some

/-- info: 'Unisono.Spec.lastPlayed_succ_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lastPlayed_succ_none

/-- info: 'Unisono.Spec.eq_none_of_lastPlayed_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.eq_none_of_lastPlayed_none

/-- info: 'Unisono.Spec.lastPlayed_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lastPlayed_some

/-- info: 'Unisono.Spec.eq_none_of_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.eq_none_of_trailing

/-- info: 'Unisono.Spec.findGreatest_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.findGreatest_isSome

/-- info: 'Unisono.Spec.missedAt_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_of_none

/-- info: 'Unisono.Spec.missedAt_of_lastPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_of_lastPlayed

/-- info: 'Unisono.Spec.one_le_missedAt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.one_le_missedAt_add

/-- info: 'Unisono.Spec.missedBefore_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedBefore_succ

/-- info: 'Unisono.Spec.missedBefore_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedBefore_mono

/-- info: 'Unisono.Spec.missedBefore_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedBefore_of_none

/-- info: 'Unisono.Spec.continuousBefore_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuousBefore_succ_of

/-- info: 'Unisono.Spec.continuousBefore_succ_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuousBefore_succ_of_not

/-- info: 'Unisono.Spec.continuousBefore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuousBefore_le

/-- info: 'Unisono.Spec.le_continuousBefore_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_continuousBefore_add

/-- info: 'Unisono.Spec.le_lastPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_lastPlayed

/-- info: 'Unisono.Spec.mem_unpassed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.mem_unpassed

/-- info: 'Unisono.Spec.PassedBefore.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PassedBefore.mono

/-- info: 'Unisono.Spec.firstFrames_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.firstFrames_eq

/-- info: 'Unisono.Spec.card_unpassed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.card_unpassed_le

/-- info: 'Unisono.Spec.neverPlayed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.neverPlayed_le

/-- info: 'Unisono.Spec.neverPlayed_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.neverPlayed_mono

/-- info: 'Unisono.Spec.neverPlayed_le_of_missed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.neverPlayed_le_of_missed

/-- info: 'Unisono.Spec.exists_time_paid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_time_paid

/-- info: 'Unisono.Spec.discontinuityAt_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuityAt_of_none

/-- info: 'Unisono.Spec.discontinuityAt_of_some_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuityAt_of_some_none

/-- info: 'Unisono.Spec.discontinuityAt_of_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuityAt_of_continuous

/-- info: 'Unisono.Spec.discontinuityAt_of_not_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuityAt_of_not_continuous

/-- info: 'Unisono.Spec.getD_lastPlayed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.getD_lastPlayed_le

/-- info: 'Unisono.Spec.getD_lastPlayed_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.getD_lastPlayed_le_of_le

/-- info: 'Unisono.Spec.stall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stall_le

/-- info: 'Unisono.Spec.stall_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stall_le_of_le

/-- info: 'Unisono.Spec.lastPlayed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lastPlayed_congr

/-- info: 'Unisono.Spec.lastPlayed_isSome_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.lastPlayed_isSome_of_le

/-- info: 'Unisono.Spec.add_le_lastPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.add_le_lastPlayed

/-- info: 'Unisono.Spec.maxPlayed_succ_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.maxPlayed_succ_some

/-- info: 'Unisono.Spec.maxPlayed_succ_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.maxPlayed_succ_none

/-- info: 'Unisono.Spec.maxPlayed_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.maxPlayed_mono

/-- info: 'Unisono.Spec.le_maxPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_maxPlayed

/-- info: 'Unisono.Spec.maxPlayed_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.maxPlayed_nonneg

/-- info: 'Unisono.Spec.NewGround.playsContinuously' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.NewGround.playsContinuously

/-- info: 'Unisono.Spec.NewGround.covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.NewGround.covers

/-- info: 'Unisono.Spec.not_covers_of_maxPlayed_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.not_covers_of_maxPlayed_lt

/-- info: 'Unisono.Spec.NewGround.maxPlayed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.NewGround.maxPlayed_eq

/-- info: 'Unisono.Spec.NewGround.add_le_maxPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.NewGround.add_le_maxPlayed

/-- info: 'Unisono.Spec.World.latency_of_newGround' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.latency_of_newGround

/-- info: 'Unisono.Spec.World.le_latency_of_newGround' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.le_latency_of_newGround

/-- info: 'Unisono.Spec.newGroundCount_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newGroundCount_succ_of

/-- info: 'Unisono.Spec.newGroundCount_succ_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newGroundCount_succ_of_not

/-- info: 'Unisono.Spec.newFrames_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newFrames_succ_of

/-- info: 'Unisono.Spec.newFrames_succ_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newFrames_succ_of_not

/-- info: 'Unisono.Spec.newGroundCount_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newGroundCount_of_le

/-- info: 'Unisono.Spec.le_floor_of_mem_newFrames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_floor_of_mem_newFrames

/-- info: 'Unisono.Spec.exists_of_mem_newFrames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_of_mem_newFrames

/-- info: 'Unisono.Spec.card_newFrames_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.card_newFrames_succ_of

/-- info: 'Unisono.Spec.newFrames_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newFrames_invariant

/-- info: 'Unisono.Spec.le_card_newFrames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_card_newFrames

/-- info: 'Unisono.Spec.replayBefore_succ_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.replayBefore_succ_of

/-- info: 'Unisono.Spec.replayBefore_succ_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.replayBefore_succ_of_not

/-- info: 'Unisono.Spec.maxPlayed_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.maxPlayed_of_none

/-- info: 'Unisono.Spec.replay_le_missed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.replay_le_missed

/-- info: 'Unisono.Spec.newGroundCount_add_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newGroundCount_add_replay

/-- info: 'Unisono.Spec.newGroundCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newGroundCount_le

/-- info: 'Unisono.Spec.le_card_newFrames_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_card_newFrames_mul

/-- info: 'Unisono.Spec.mem_newFrames_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.mem_newFrames_of

/-- info: 'Unisono.Spec.newFrames_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newFrames_subset

/-- info: 'Unisono.Spec.disjoint_newFrames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.disjoint_newFrames

/-- info: 'Unisono.Spec.sum_blocks_newFrames_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_blocks_newFrames_le

/-- info: 'Unisono.Spec.World.sum_le_accruedFrames_latency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sum_le_accruedFrames_latency

/-- info: 'Unisono.Spec.World.sum_le_accruedOutputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sum_le_accruedOutputs

/-- info: 'Unisono.Spec.World.longRun_le_cost_of_latency_missed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.longRun_le_cost_of_latency_missed

/-- info: 'Unisono.Spec.getD_lastPlayed_le_maxPlayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.getD_lastPlayed_le_maxPlayed

/-- info: 'Unisono.Spec.replayBefore_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.replayBefore_mono

/-- info: 'Unisono.Spec.sum_blocks_losses_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_blocks_losses_le

/-- info: 'Unisono.Spec.continuousBefore_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.continuousBefore_le_add

/-- info: 'Unisono.Spec.CaptureDevice.mul_le_capture_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.mul_le_capture_sub

/-- info: 'Unisono.Spec.PlaybackDevice.out_sub_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.out_sub_le_mul

/-- info: 'Unisono.Spec.World.le_handed_blockFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.le_handed_blockFrom

/-- info: 'Unisono.Spec.World.handed_lt_of_lt_blockFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.handed_lt_of_lt_blockFrom

/-- info: 'Unisono.Spec.newGroundCount_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.newGroundCount_of_none

/-- info: 'Unisono.Spec.unplayedAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.unplayedAt_of

/-- info: 'Unisono.Spec.unplayedAt_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.unplayedAt_of_not

/-- info: 'Unisono.Spec.neverPlayed_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.neverPlayed_eq_sum

/-- info: 'Unisono.Spec.playTime_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.playTime_isSome_iff

/-- info: 'Unisono.Spec.ofReal_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ofReal_sum_le

/-- info: 'Unisono.Spec.speakerShiftCost_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.speakerShiftCost_nonneg

/-- info: 'Unisono.Spec.World.pairCost_add_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.pairCost_add_ge

/-- info: 'Unisono.Spec.World.trackingAt_add_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.trackingAt_add_ge

/-- info: 'Unisono.Spec.World.frame_add_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.frame_add_ge

/-- info: 'Unisono.Spec.find_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.find_of_linear

/-- info: 'Unisono.Spec.exists_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_of_linear

/-- info: 'Unisono.Spec.World.accruedFrames_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.accruedFrames_eq_sum

/-- info: 'Unisono.Spec.World.accruedFrames_congr_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.accruedFrames_congr_source

/-- info: 'Unisono.Spec.World.weighted_missed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.weighted_missed_eq

/-- info: 'Unisono.Spec.World.weighted_frames_add_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.weighted_frames_add_ge

/-- info: 'Unisono.Spec.World.cost_add_ge_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.cost_add_ge_of_shift

/-- info: 'Unisono.Spec.le_longRun_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.le_longRun_of_linear

/-- info: 'Unisono.Spec.missedBefore_ge_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedBefore_ge_of_none

/-- info: 'Unisono.Spec.World.cost_ge_of_eventually_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.cost_ge_of_eventually_none

/-- info: 'Unisono.Spec.World.captured_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.captured_of_linear

/-- info: 'Unisono.Spec.World.advance_of_speed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.advance_of_speed

/-- info: 'Unisono.Spec.Solution.nonneg_of_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.nonneg_of_plays

/-- info: 'Unisono.Spec.Solution.plays_eq_none_of_stalled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_eq_none_of_stalled

/-- info: 'Unisono.Spec.mul_shiftCost_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.mul_shiftCost_le_sum

/-- info: 'Unisono.Spec.Solution.cost_shiftStar_add_ge_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.cost_shiftStar_add_ge_of_step

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

/-- info: 'Unisono.Spec.GenerativeWorld.hasLaw_canonicalDraw_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.hasLaw_canonicalDraw_split

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

/-- info: 'Unisono.Spec.Clock.ext_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Clock.ext_read

/-- info: 'Unisono.Spec.CaptureDevice.ext_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.ext_fields

/-- info: 'Unisono.Spec.PlaybackDevice.ext_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.ext_fields

/-- info: 'Unisono.Spec.Network.ext_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Network.ext_fields

/-- info: 'Unisono.Spec.World.ext_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.ext_fields

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.ext_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.ext_fields

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.unique

/-- info: 'Unisono.Spec.GenerativeWorld.Component.measurable_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Component.measurable_scalar

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.coordinates_eq_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.coordinates_eq_scalar

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalDraw_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalDraw_coordinates

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_canonicalDraw_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_canonicalDraw_split

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_canonicalDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_canonicalDraw

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.coordinates_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.coordinates_law

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_eq_canonicalDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_eq_canonicalDraw

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_eq_canonicalWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_eq_canonicalWorld

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_of_ae_canonicalDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_of_ae_canonicalDraw

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.ae_of_ae_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.ae_of_ae_canonical

/-- info: 'Unisono.Spec.GenerativeWorld.Prior.lintegral_eq_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Prior.lintegral_eq_canonical

/-- info: 'Unisono.Spec.updatePair_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.updatePair_right

/-- info: 'Unisono.Spec.updatePair_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.updatePair_left

/-- info: 'Unisono.Spec.updatePair_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.updatePair_of_ne

/-- info: 'Unisono.Spec.measurable_updatePair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_updatePair

/-- info: 'Unisono.Spec.measurePreserving_updatePair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurePreserving_updatePair

/-- info: 'Unisono.Spec.measurePreserving_restrict_of_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurePreserving_restrict_of_eqOn

/-- info: 'Unisono.Spec.GenerativeWorld.reflectPair_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectPair_shift

/-- info: 'Unisono.Spec.GenerativeWorld.measurable_reflectPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurable_reflectPair

/-- info: 'Unisono.Spec.GenerativeWorld.measurePreserving_reflectPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurePreserving_reflectPair

/-- info: 'Unisono.Spec.GenerativeWorld.idealWorld_shiftStarKeepPeers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.idealWorld_shiftStarKeepPeers

/-- info: 'Unisono.Spec.GenerativeWorld.senderSplit_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.senderSplit_injective

/-- info: 'Unisono.Spec.GenerativeWorld.senderSplit_ne_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.senderSplit_ne_offset

/-- info: 'Unisono.Spec.GenerativeWorld.reflectList_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectList_of_ne

/-- info: 'Unisono.Spec.GenerativeWorld.reflectList_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectList_apply

/-- info: 'Unisono.Spec.GenerativeWorld.measurePreserving_reflectHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurePreserving_reflectHost

/-- info: 'Unisono.Spec.GenerativeWorld.measurePreserving_reflectList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurePreserving_reflectList

/-- info: 'Unisono.Spec.GenerativeWorld.measurePreserving_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measurePreserving_reflect

/-- info: 'Unisono.Spec.GenerativeWorld.reflect_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflect_apply

/-- info: 'Unisono.Spec.GenerativeWorld.reflect_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflect_of_ne

/-- info: 'Unisono.Spec.GenerativeWorld.reflectShift_sender' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectShift_sender

/-- info: 'Unisono.Spec.GenerativeWorld.reflect_split_sender' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflect_split_sender

/-- info: 'Unisono.Spec.GenerativeWorld.reflect_split_peer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflect_split_peer

/-- info: 'Unisono.Spec.GenerativeWorld.reflect_delay_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflect_delay_star

/-- info: 'Unisono.Spec.GenerativeWorld.reflectShift_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectShift_star

/-- info: 'Unisono.Spec.GenerativeWorld.canonicalWorld_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.canonicalWorld_reflect

/-- info: 'Unisono.Spec.GenerativeWorld.almostSurely_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.almostSurely_iff

/-- info: 'Unisono.Spec.GenerativeWorld.aemeasurable_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.aemeasurable_cost

/-- info: 'Unisono.Spec.GenerativeWorld.expectedCost_eq_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.expectedCost_eq_canonical

/-- info: 'Unisono.Spec.GenerativeWorld.capture_unbounded_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.capture_unbounded_canonical

/-- info: 'Unisono.Spec.GenerativeWorld.StarSolutions.le_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.StarSolutions.le_canonical

/-- info: 'Unisono.Spec.GenerativeWorld.StarSolutions.le_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.StarSolutions.le_expectedCost

/-- info: 'Unisono.Spec.meanFin_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.meanFin_const_add

/-- info: 'Unisono.Spec.varFin_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.varFin_const_add

/-- info: 'Unisono.Spec.frameCost_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.frameCost_const_add

/-- info: 'Unisono.Spec.shiftCost_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.shiftCost_neg

/-- info: 'Unisono.Spec.shiftCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.shiftCost_le

/-- info: 'Unisono.Spec.ofReal_shiftCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ofReal_shiftCost

/-- info: 'Unisono.Spec.World.PlaysAtLatencies.exists_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.PlaysAtLatencies.exists_covers

/-- info: 'Unisono.Spec.World.PlaysAtLatencies.exists_playTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.PlaysAtLatencies.exists_playTime

/-- info: 'Unisono.Spec.World.frameCost_le_cost_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.frameCost_le_cost_of_exact

/-- info: 'Unisono.Spec.Solution.handled_asked_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_asked_time

/-- info: 'Unisono.Solutions.FixedDelay.act_sends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.act_sends

/-- info: 'Unisono.Solutions.FixedDelay.inFlight_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.inFlight_provenance

/-- info: 'Unisono.Spec.IdealConstantWorld.Holds.out_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.Holds.out_unbounded

/-- info: 'Unisono.Spec.IdealConstantWorld.Holds.capture_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.IdealConstantWorld.Holds.capture_unbounded

/-- info: 'Unisono.Solutions.FixedDelay.playsAtLatencies_of_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.playsAtLatencies_of_ideal

/-- info: 'Unisono.Solutions.FixedDelay.playTime_of_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.playTime_of_ideal

/-- info: 'Unisono.Solutions.FixedDelay.cost_eq_of_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.cost_eq_of_ideal

/-- info: 'Unisono.Spec.measurable_shiftCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.measurable_shiftCost

/-- info: 'Unisono.Spec.cond_volume_Icc_compl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.cond_volume_Icc_compl_le

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.measurable_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.measurable_split

/-- info: 'Unisono.Spec.GenerativeWorld.Draw.measurable_asymmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Draw.measurable_asymmetry

/-- info: 'Unisono.Spec.GenerativeWorld.abs_asymmetry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.abs_asymmetry_le

/-- info: 'Unisono.Spec.GenerativeWorld.reflectScale_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectScale_mul

/-- info: 'Unisono.Spec.GenerativeWorld.reflectShift_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.reflectShift_of_mem

/-- info: 'Unisono.Spec.GenerativeWorld.measure_reflect_out_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.measure_reflect_out_le

/-- info: 'Unisono.Spec.GenerativeWorld.lintegral_asymmetry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.lintegral_asymmetry_le

/-- info: 'Unisono.Solutions.FixedDelay.asymmetry_idealWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.asymmetry_idealWorld

/-- info: 'Unisono.Solutions.FixedDelay.margin_idealWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.margin_idealWorld

/-- info: 'Unisono.Solutions.FixedDelay.chosen_of_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.chosen_of_plays

/-- info: 'Unisono.Solutions.FixedDelay.step_le_slew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.step_le_slew

/-- info: 'Unisono.Solutions.FixedDelay.withinStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.withinStep

/-- info: 'Unisono.Solutions.FixedDelay.withinSpeed_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.withinSpeed_of_linear

/-- info: 'Unisono.Spec.speakerShiftCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.speakerShiftCost_le

/-- info: 'Unisono.Spec.GenerativeWorld.abs_reflectShift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.abs_reflectShift_le

/-- info: 'Unisono.Spec.GenerativeWorld.MissedWeightPays.threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.MissedWeightPays.threshold

/-- info: 'Unisono.Solutions.FixedDelay.ae_idealWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.ae_idealWorld

/-- info: 'Unisono.Solutions.FixedDelay.ae_cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.ae_cost_eq

/-- info: 'Unisono.Solutions.FixedDelay.starSolutions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.starSolutions

/-- info: 'Unisono.Solutions.FixedDelay.within_starMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.within_starMargin

/-- info: 'Unisono.Solutions.FixedDelay.within_starMargin_conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.within_starMargin_conditions

/-- info: 'Unisono.Spec.State.fields_of_withoutPlays_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.fields_of_withoutPlays_eq

/-- info: 'Unisono.Spec.State.sendAll_withoutPlays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.sendAll_withoutPlays

/-- info: 'Unisono.Spec.State.handle_withoutPlays_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.handle_withoutPlays_eq

/-- info: 'Unisono.Spec.State.handle_withoutPlays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.handle_withoutPlays

/-- info: 'Unisono.Spec.State.step_withoutPlays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.step_withoutPlays

/-- info: 'Unisono.Spec.Solution.states_withoutPlays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.states_withoutPlays

/-- info: 'Unisono.Spec.Solution.views_eq_of_sends_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.views_eq_of_sends_eq

/-- info: 'Unisono.Spec.Solution.held_eq_of_sends_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.held_eq_of_sends_eq

/-- info: 'Unisono.Spec.Solution.askedNext_eq_of_sends_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.askedNext_eq_of_sends_eq

/-- info: 'Unisono.Spec.Solution.earliest_eq_of_sends_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.earliest_eq_of_sends_eq

/-- info: 'Unisono.Spec.Solution.handled_eq_of_sends_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_eq_of_sends_eq

/-- info: 'Unisono.Spec.Solution.eventTime_eq_of_sends_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.eventTime_eq_of_sends_eq

/-- info: 'Unisono.Spec.Observation.frames_mapMsg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Observation.frames_mapMsg

/-- info: 'Unisono.Spec.State.forget_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_send

/-- info: 'Unisono.Spec.State.forget_sendAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_sendAll

/-- info: 'Unisono.Spec.State.forget_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_observe

/-- info: 'Unisono.Spec.State.forget_addTimers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_addTimers

/-- info: 'Unisono.Spec.State.forget_withoutPlays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_withoutPlays

/-- info: 'Unisono.Spec.State.forget_handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_handle

/-- info: 'Unisono.Spec.State.forget_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_key

/-- info: 'Unisono.Spec.State.forget_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_due

/-- info: 'Unisono.Spec.State.forget_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.forget_step

/-- info: 'Unisono.Spec.Solution.states_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.states_forget

/-- info: 'Unisono.Spec.Solution.views_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.views_forget

/-- info: 'Unisono.Spec.Solution.held_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.held_forget

/-- info: 'Unisono.Spec.Solution.askedNext_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.askedNext_forget

/-- info: 'Unisono.Spec.Solution.earliest_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.earliest_forget

/-- info: 'Unisono.Spec.Solution.handled_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_forget

/-- info: 'Unisono.Spec.Solution.eventTime_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.eventTime_forget

/-- info: 'Unisono.Solutions.Controller.twoExchanges_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.twoExchanges_exact

/-- info: 'Unisono.Solutions.Controller.twoReports_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.twoReports_exact

/-- info: 'Unisono.Solutions.Controller.plain_enrich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.plain_enrich

/-- info: 'Unisono.Solutions.Controller.sendsMore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.sendsMore

/-- info: 'Unisono.Solutions.Controller.plays_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.plays_asked

/-- info: 'Unisono.Solutions.Controller.levelAt_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.levelAt_of_mem

/-- info: 'Unisono.Solutions.Controller.lt_of_levelAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lt_of_levelAt

/-- info: 'Unisono.Solutions.Controller.Header.eq_of_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.Header.eq_of_due

/-- info: 'Unisono.Solutions.Controller.Header.due_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.Header.due_of_eq

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.clock

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.deviceReading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.deviceReading

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantDelays.deliver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantDelays.deliver

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.capture

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.capture_reported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.capture_reported

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.out

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.speaker_reported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.speaker_reported

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.asked

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.hostPaused_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.hostPaused_mono

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.asked_lt_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.asked_lt_out

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.asked_lt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.asked_lt_of_le

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.captured

/-- info: 'Unisono.Spec.GenerativeWorld.abs_inv_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.abs_inv_sub_one_le

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantDelays.withinBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantDelays.withinBounds

/-- info: 'Unisono.Spec.CaptureDevice.head?_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.head?_block

/-- info: 'Unisono.Spec.PlaybackDevice.head?_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.head?_block

/-- info: 'Unisono.Solutions.FixedDelay.act_sends_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.act_sends_block

/-- info: 'Unisono.Solutions.Controller.exchangesOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exchangesOf_eq

/-- info: 'Unisono.Solutions.Controller.mem_plainExchangesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_plainExchangesOf

/-- info: 'Unisono.Solutions.Controller.plainExchangesOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.plainExchangesOf_mem

/-- info: 'Unisono.Solutions.Controller.mem_headersOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_headersOf

/-- info: 'Unisono.Solutions.Controller.headersOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.headersOf_mem

/-- info: 'Unisono.Solutions.Controller.headersOf_append_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.headersOf_append_asked

/-- info: 'Unisono.Solutions.Controller.mem_playbackReports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_playbackReports

/-- info: 'Unisono.Solutions.Controller.mem_captureReports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_captureReports

/-- info: 'Unisono.Solutions.Controller.sends_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.sends_block

/-- info: 'Unisono.Solutions.Controller.block_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.block_header

/-- info: 'Unisono.Solutions.Controller.exchange_of_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exchange_of_view

/-- info: 'Unisono.Solutions.Controller.exists_two_exchanges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_two_exchanges

/-- info: 'Unisono.Solutions.Controller.handedNext_of_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.handedNext_of_handled

/-- info: 'Unisono.Solutions.Controller.captureLine_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.captureLine_exact

/-- info: 'Unisono.Solutions.Controller.playbackLine_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.playbackLine_exact

/-- info: 'Unisono.Solutions.Controller.IsDue.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.IsDue.unique

/-- info: 'Unisono.Solutions.Controller.isDue_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.isDue_iff

/-- info: 'Unisono.Solutions.Controller.exists_isDue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_isDue

/-- info: 'Unisono.Solutions.Controller.speaker_plays_of_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.speaker_plays_of_levels

/-- info: 'Unisono.Solutions.Controller.speaker_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.speaker_exact

/-- info: 'Unisono.Solutions.Controller.playsAtLatencies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.playsAtLatencies

/-- info: 'Unisono.Solutions.Controller.playsAtLatencies_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.playsAtLatencies_example

/-- info: 'Unisono.Spec.Solution.held_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.held_succ

/-- info: 'Unisono.Spec.Solution.mem_held_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.mem_held_iff

/-- info: 'Unisono.Spec.Solution.received_lt_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.received_lt_asked

/-- info: 'Unisono.Spec.Solution.handedNext_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handedNext_mono

/-- info: 'Unisono.Spec.Solution.earliest_of_handled_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.earliest_of_handled_handed

/-- info: 'Unisono.Spec.Solution.handed_step_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handed_step_unique

/-- info: 'Unisono.Spec.Solution.handled_of_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handled_of_handed

/-- info: 'Unisono.Spec.Solution.handedNext_of_earliest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handedNext_of_earliest

/-- info: 'Unisono.Spec.Solution.frame_times' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.frame_times

/-- info: 'Unisono.Spec.Solution.arrival_le_of_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.arrival_le_of_held

/-- info: 'Unisono.Spec.Solution.arrival_lt_asked_of_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.arrival_lt_asked_of_plays

/-- info: 'Unisono.Spec.earliest_eq_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.earliest_eq_of_agree

/-- info: 'Unisono.Spec.forall₂_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.forall₂_getElem?

/-- info: 'Unisono.Spec.forall₂_eraseIdx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Unisono.Spec.forall₂_eraseIdx

/-- info: 'Unisono.Spec.InFlight.SameBefore.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.InFlight.SameBefore.refl

/-- info: 'Unisono.Spec.InFlight.SameBefore.eq_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.InFlight.SameBefore.eq_of_lt

/-- info: 'Unisono.Spec.State.SameBefore.due_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.SameBefore.due_eq

/-- info: 'Unisono.Spec.State.SameBefore.send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.SameBefore.send

/-- info: 'Unisono.Spec.State.SameBefore.sendAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.SameBefore.sendAll

/-- info: 'Unisono.Spec.State.SameBefore.handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.SameBefore.handle

/-- info: 'Unisono.Spec.State.SameBefore.key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.SameBefore.key

/-- info: 'Unisono.Spec.State.SameBefore.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.SameBefore.step

/-- info: 'Unisono.Spec.Solution.sameBefore_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.sameBefore_states

/-- info: 'Unisono.Spec.Solution.plays_eq_of_sameBefore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_eq_of_sameBefore

/-- info: 'Unisono.Spec.limitStep_none_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitStep_none_left

/-- info: 'Unisono.Spec.limitStep_none_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitStep_none_right

/-- info: 'Unisono.Spec.limitStep_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitStep_eq_some

/-- info: 'Unisono.Spec.limitStep_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitStep_within

/-- info: 'Unisono.Spec.limitStep_of_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitStep_of_within

/-- info: 'Unisono.Spec.limitAt_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitAt_eq_some

/-- info: 'Unisono.Spec.limitAt_range'_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitAt_range'_first

/-- info: 'Unisono.Spec.limitAt_range'_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitAt_range'_succ

/-- info: 'Unisono.Spec.limitLast_range'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limitLast_range'

/-- info: 'Unisono.Spec.foldl_limiterStep_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.foldl_limiterStep_fst

/-- info: 'Unisono.Spec.limiterLast_concat_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limiterLast_concat_asked

/-- info: 'Unisono.Spec.limiterLast_concat_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limiterLast_concat_of_ne

/-- info: 'Unisono.Spec.limiterLast_append_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.limiterLast_append_of_ne

/-- info: 'Unisono.Spec.Solution.limited_plays_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_plays_asked

/-- info: 'Unisono.Spec.Solution.asked_step_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.asked_step_unique

/-- info: 'Unisono.Spec.Solution.limiterLast_at_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limiterLast_at_next

/-- info: 'Unisono.Spec.Solution.limited_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_views

/-- info: 'Unisono.Spec.Solution.limited_asked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_asked_iff

/-- info: 'Unisono.Spec.Solution.limited_chosenAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_chosenAt

/-- info: 'Unisono.Spec.Solution.limited_chosenAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_chosenAt_succ

/-- info: 'Unisono.Spec.Solution.limited_withinStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_withinStep

/-- info: 'Unisono.Spec.Solution.limited_plays_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_plays_eq_some

/-- info: 'Unisono.Spec.Solution.limited_plays_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.limited_plays_eq

/-- info: 'Unisono.Spec.stepAt_range'_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepAt_range'_first

/-- info: 'Unisono.Spec.stepAt_range'_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepAt_range'_succ

/-- info: 'Unisono.Spec.stepLast_range'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepLast_range'

/-- info: 'Unisono.Spec.foldl_carryStep_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.foldl_carryStep_fst

/-- info: 'Unisono.Spec.carried_concat_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.carried_concat_asked

/-- info: 'Unisono.Spec.carried_concat_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.carried_concat_of_ne

/-- info: 'Unisono.Spec.carried_append_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.carried_append_of_ne

/-- info: 'Unisono.Spec.Solution.stepped_plays_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_plays_asked

/-- info: 'Unisono.Spec.Solution.carried_at_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.carried_at_next

/-- info: 'Unisono.Spec.Solution.stepped_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_views

/-- info: 'Unisono.Spec.Solution.stepped_asked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_asked_iff

/-- info: 'Unisono.Spec.Solution.stepped_chosenAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_chosenAt

/-- info: 'Unisono.Spec.Solution.stepped_chosenAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_chosenAt_succ

/-- info: 'Unisono.Spec.followStep_of_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_of_within

/-- info: 'Unisono.Spec.followStep_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_within

/-- info: 'Unisono.Spec.Solution.followed_withinStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.followed_withinStep

/-- info: 'Unisono.Spec.followStep_none_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_none_left

/-- info: 'Unisono.Spec.followStep_none_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_none_right

/-- info: 'Unisono.Spec.followStep_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_eq_none

/-- info: 'Unisono.Spec.followStep_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_error_le

/-- info: 'Unisono.Spec.Solution.followed_plays_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.followed_plays_eq

/-- info: 'Unisono.Spec.handoversOf_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.handoversOf_append

/-- info: 'Unisono.Spec.requestsOf_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.requestsOf_append

/-- info: 'Unisono.Spec.World.blockLength_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.blockLength_pos

/-- info: 'Unisono.Spec.Solution.handoversOf_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handoversOf_views

/-- info: 'Unisono.Spec.Solution.requestsOf_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.requestsOf_views

/-- info: 'Unisono.Spec.Solution.handoverView_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handoverView_eq

/-- info: 'Unisono.Spec.Solution.handoverView_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handoverView_succ

/-- info: 'Unisono.Spec.Solution.askedNext_of_earliest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.askedNext_of_earliest

/-- info: 'Unisono.Spec.Solution.requestsOf_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.requestsOf_request

/-- info: 'Unisono.Spec.Solution.handoversOf_handoverView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.handoversOf_handoverView

/-- info: 'Unisono.Spec.Solution.requestView_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.requestView_eq

/-- info: 'Unisono.Spec.World.knot_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knot_strictMono

/-- info: 'Unisono.Spec.World.handedReading_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.handedReading_mono

/-- info: 'Unisono.Spec.knotStep_snd_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.knotStep_snd_pos

/-- info: 'Unisono.Spec.knotStep_snd_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.knotStep_snd_mem

/-- info: 'Unisono.Spec.World.knotInc_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotInc_pos

/-- info: 'Unisono.Spec.World.knotInc_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotInc_mem

/-- info: 'Unisono.Spec.World.knot_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knot_succ

/-- info: 'Unisono.Spec.World.knot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knot_zero

/-- info: 'Unisono.Spec.World.knot_succ_eq_knotInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knot_succ_eq_knotInput

/-- info: 'Unisono.Spec.World.knotPeriod_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotPeriod_zero

/-- info: 'Unisono.Spec.World.knotStart_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotStart_add

/-- info: 'Unisono.Spec.World.knotStart_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotStart_succ

/-- info: 'Unisono.Spec.World.knotPeriod_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotPeriod_pos

/-- info: 'Unisono.Spec.World.knotPeriod_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotPeriod_mem

/-- info: 'Unisono.Spec.World.knotTime_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotTime_right

/-- info: 'Unisono.Spec.World.knotTime_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotTime_left

/-- info: 'Unisono.Spec.missedAt_le_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_le_abs

/-- info: 'Unisono.Spec.World.captured_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.captured_of_mem

/-- info: 'Unisono.Spec.World.mul_le_captured_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.mul_le_captured_sub

/-- info: 'Unisono.Spec.World.captured_sub_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.captured_sub_le_mul

/-- info: 'Unisono.Spec.World.latency_eq_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.latency_eq_of_some

/-- info: 'Unisono.Spec.World.latency_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.latency_between

/-- info: 'Unisono.Spec.PlaybackDevice.block_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.block_unique

/-- info: 'Unisono.Spec.PlaybackDevice.exists_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.exists_block

/-- info: 'Unisono.Spec.PlaybackDevice.mem_blockOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.mem_blockOf

/-- info: 'Unisono.Spec.PlaybackDevice.blockOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.blockOf_eq

/-- info: 'Unisono.Spec.followStep_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_gap

/-- info: 'Unisono.Spec.Solution.chosen_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.chosen_eq

/-- info: 'Unisono.Spec.Solution.plays_eq_playable_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_eq_playable_chosen

/-- info: 'Unisono.Spec.Solution.stepped_chosen_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_chosen_succ

/-- info: 'Unisono.Spec.stepOver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepOver_nonneg

/-- info: 'Unisono.Spec.followDist_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followDist_nonneg

/-- info: 'Unisono.Spec.abs_le_add_stepOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.abs_le_add_stepOver

/-- info: 'Unisono.Spec.abs_sub_le_sum_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.abs_sub_le_sum_steps

/-- info: 'Unisono.Spec.Follows.target_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.target_of_some

/-- info: 'Unisono.Spec.Follows.dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.dist_le

/-- info: 'Unisono.Spec.Follows.followDist_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.followDist_succ_le

/-- info: 'Unisono.Spec.followDist_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followDist_of_some

/-- info: 'Unisono.Spec.followDist_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followDist_of_none

/-- info: 'Unisono.Spec.jumpAt_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.jumpAt_of_none

/-- info: 'Unisono.Spec.jumpAt_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.jumpAt_of_some

/-- info: 'Unisono.Spec.Follows.sum_jumpAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.sum_jumpAt_le

/-- info: 'Unisono.Spec.follower_of_played' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.follower_of_played

/-- info: 'Unisono.Spec.missedAt_of_lastPlayed_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_of_lastPlayed_none

/-- info: 'Unisono.Spec.Follows.missedAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.missedAt_le

/-- info: 'Unisono.Spec.Follows.sum_missedAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.sum_missedAt_le

/-- info: 'Unisono.Spec.Follows.discontinuityAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.discontinuityAt_le

/-- info: 'Unisono.Spec.Follows.sum_discontinuityAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.sum_discontinuityAt_le

/-- info: 'Unisono.Spec.heldTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.heldTarget_eq

/-- info: 'Unisono.Spec.stepOver_heldTarget_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.stepOver_heldTarget_of_none

/-- info: 'Unisono.Spec.PlaybackDevice.zero_mem_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.zero_mem_block

/-- info: 'Unisono.Spec.Solution.stepped_chosen_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_chosen_zero

/-- info: 'Unisono.Spec.Solution.followed_follows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.followed_follows

/-- info: 'Unisono.Spec.Solution.plays_none_or_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_none_or_chosen

/-- info: 'Unisono.Spec.Solution.followed_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.followed_progress

/-- info: 'Unisono.Spec.Solution.followed_sum_missedAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.followed_sum_missedAt_le

/-- info: 'Unisono.Spec.Solution.followed_sum_discontinuityAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.followed_sum_discontinuityAt_le

/-- info: 'Unisono.Spec.exists_followStep_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_followStep_eq_some

/-- info: 'Unisono.Spec.followStep_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_near

/-- info: 'Unisono.Spec.followStep_near_of_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followStep_near_of_dist_le

/-- info: 'Unisono.Spec.followed_near_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followed_near_dist_le

/-- info: 'Unisono.Spec.followed_near_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.followed_near_settles

/-- info: 'Unisono.Spec.Solution.views_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.views_pairwise

/-- info: 'Unisono.Spec.Solution.requestView_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.requestView_pairwise

/-- info: 'Unisono.Spec.Solution.stepped_isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.stepped_isStar

/-- info: 'Unisono.Spec.earliest_spec_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.earliest_spec_first

/-- info: 'Unisono.Spec.World.hostIndex_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.hostIndex_le

/-- info: 'Unisono.Spec.World.hostIndex_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.hostIndex_injective

/-- info: 'Unisono.Spec.State.arrival_mem_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.State.arrival_mem_of_lt

/-- info: 'Unisono.Spec.GenerativeWorld.IsBacklog.backlog_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IsBacklog.backlog_eq

/-- info: 'Unisono.Spec.GenerativeWorld.IsBacklog.nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IsBacklog.nonneg

/-- info: 'Unisono.Spec.GenerativeWorld.IsBacklog.add_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.IsBacklog.add_le_add

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.deliver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.deliver

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.le_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.le_arrival

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_mono

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.handed

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.handed_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.handed_unbounded

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.asked_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.asked_unbounded

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantRates.arrival_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantRates.arrival_mono

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantDelays.toConstantRates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantDelays.toConstantRates

/-- info: 'Unisono.Spec.GenerativeWorld.ConstantDelays.arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.ConstantDelays.arrival

/-- info: 'Unisono.Solutions.FixedDelay.progress_of_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.progress_of_unbounded

/-- info: 'Unisono.Solutions.FixedDelay.request_step_of_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.request_step_of_unbounded

/-- info: 'Unisono.Spec.CaptureDevice.block_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.block_unique

/-- info: 'Unisono.Solutions.FixedDelay.block_inFlight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_inFlight

/-- info: 'Unisono.Solutions.FixedDelay.block_arrives_of_noLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_arrives_of_noLoss

/-- info: 'Unisono.Solutions.FixedDelay.block_handled_of_noLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.block_handled_of_noLoss

/-- info: 'Unisono.Solutions.FixedDelay.inFlight_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.inFlight_frames

/-- info: 'Unisono.Solutions.FixedDelay.held_of_noLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.held_of_noLoss

/-- info: 'Unisono.Solutions.FixedDelay.mem_held_iff_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.mem_held_iff_arrived

/-- info: 'Unisono.Solutions.Controller.leastRoundTrip_exactFromLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.leastRoundTrip_exactFromLeast

/-- info: 'Unisono.Solutions.Controller.captured_duePosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.captured_duePosition

/-- info: 'Unisono.Solutions.Controller.duePosition_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.duePosition_succ

/-- info: 'Unisono.Solutions.Controller.exchange_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exchange_lines

/-- info: 'Unisono.Solutions.Controller.exchange_of_built' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exchange_of_built

/-- info: 'Unisono.Solutions.Controller.speaker_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.speaker_plays

/-- info: 'Unisono.Solutions.Controller.speaker_chooses_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.speaker_chooses_plays

/-- info: 'Unisono.Solutions.Controller.speaker_chooses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.speaker_chooses

/-- info: 'Unisono.Solutions.Controller.abs_slopeTo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_slopeTo_le

/-- info: 'Unisono.Solutions.Controller.levelStep_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.levelStep_level

/-- info: 'Unisono.Solutions.Controller.foldl_levelStep_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.foldl_levelStep_level

/-- info: 'Unisono.Solutions.Controller.levelState_aim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.levelState_aim

/-- info: 'Unisono.Solutions.Controller.sum_needCost_aimAfter_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.sum_needCost_aimAfter_sub_le

/-- info: 'Unisono.Solutions.Controller.announced_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announced_eq

/-- info: 'Unisono.Solutions.Controller.announced_steppedLevel_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announced_steppedLevel_succ

/-- info: 'Unisono.Solutions.Controller.abs_announced_slope_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_announced_slope_le

/-- info: 'Unisono.Solutions.Controller.levelStep_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.levelStep_mem

/-- info: 'Unisono.Solutions.Controller.levelState_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.levelState_mem

/-- info: 'Unisono.Solutions.Controller.announced_fst_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announced_fst_mem

/-- info: 'Unisono.Solutions.Controller.exists_handover_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_handover_step

/-- info: 'Unisono.Solutions.Controller.speaker_plays_of_steppedLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.speaker_plays_of_steppedLevel

/-- info: 'Unisono.Solutions.Controller.arrival_lt_asked_of_needOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrival_lt_asked_of_needOf_le

/-- info: 'Unisono.Solutions.Controller.level_lt_needOf_of_silent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.level_lt_needOf_of_silent

/-- info: 'Unisono.Solutions.Controller.needOfBlock_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.needOfBlock_eq

/-- info: 'Unisono.Solutions.Controller.isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.isStar

/-- info: 'Unisono.Solutions.Controller.combined_isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.combined_isStar

/-- info: 'Unisono.Solutions.Controller.combined_withinStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.combined_withinStep

/-- info: 'Unisono.Solutions.Controller.Rules.plain_enrich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.Rules.plain_enrich

/-- info: 'Unisono.Solutions.Controller.ruled_sendsMore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_sendsMore

/-- info: 'Unisono.Solutions.Controller.ruled_isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_isStar

/-- info: 'Unisono.Solutions.Controller.ruled_plays_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_plays_asked

/-- info: 'Unisono.Solutions.Controller.ruled_sends_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_sends_block

/-- info: 'Unisono.Solutions.Controller.ruled_block_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_block_header

/-- info: 'Unisono.Solutions.Controller.ruled_block_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_block_origin

/-- info: 'Unisono.Solutions.Controller.ruled_received_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_received_block

/-- info: 'Unisono.Solutions.Controller.ruled_received_stamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_received_stamp

/-- info: 'Unisono.Solutions.Controller.ruled_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_chosen

/-- info: 'Unisono.Solutions.Controller.knotCapture_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotCapture_eq

/-- info: 'Unisono.Solutions.Controller.handedCount_handedEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.handedCount_handedEvent

/-- info: 'Unisono.Solutions.Controller.handedStamp_handedEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.handedStamp_handedEvent

/-- info: 'Unisono.Solutions.Controller.knotsOf_concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotsOf_concat

/-- info: 'Unisono.Solutions.Controller.knotStep_knotsOf_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotStep_knotsOf_range

/-- info: 'Unisono.Solutions.Controller.runHeader_knots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.runHeader_knots

/-- info: 'Unisono.Solutions.Controller.ruled_chosen_knots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_chosen_knots

/-- info: 'Unisono.Solutions.Controller.envelope_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.envelope_isSome

/-- info: 'Unisono.Solutions.Controller.le_of_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.le_of_envelope

/-- info: 'Unisono.Solutions.Controller.exists_of_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_of_envelope

/-- info: 'Unisono.Solutions.Controller.le_envelopeReading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.le_envelopeReading

/-- info: 'Unisono.Solutions.Controller.exists_envelopeReading_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_envelopeReading_eq

/-- info: 'Unisono.Solutions.Controller.mem_arrivalsOf_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_arrivalsOf_run

/-- info: 'Unisono.Solutions.Controller.reading_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.reading_le

/-- info: 'Unisono.Solutions.Controller.exists_reading_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_reading_eq

/-- info: 'Unisono.Solutions.Controller.mem_arrivalsOf_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_arrivalsOf_of_window

/-- info: 'Unisono.Solutions.Controller.arrivalsOf_append_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrivalsOf_append_asked

/-- info: 'Unisono.Solutions.Controller.deviceRatio_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.deviceRatio_mem

/-- info: 'Unisono.Solutions.Controller.arrivalSlope_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrivalSlope_mem

/-- info: 'Unisono.Solutions.Controller.firstOutput_askedEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.firstOutput_askedEvent

/-- info: 'Unisono.Solutions.Controller.requestOutput_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.requestOutput_eq

/-- info: 'Unisono.Solutions.Controller.timed_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_chosen

/-- info: 'Unisono.Solutions.Controller.checkedReading_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.checkedReading_eq_some

/-- info: 'Unisono.Solutions.Controller.mem_recentExchanges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_recentExchanges

/-- info: 'Unisono.Solutions.Controller.halfTrip_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.halfTrip_mem

/-- info: 'Unisono.Solutions.Controller.halfTrip_le_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.halfTrip_le_of_mem

/-- info: 'Unisono.Solutions.Controller.le_halfTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.le_halfTrip

/-- info: 'Unisono.Solutions.Controller.mem_windowArrivals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_windowArrivals

/-- info: 'Unisono.Solutions.Controller.ratioAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ratioAt_mem

/-- info: 'Unisono.Solutions.Controller.ruled_request_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_request_step

/-- info: 'Unisono.Solutions.Controller.ruled_handover_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_handover_step

/-- info: 'Unisono.Solutions.Controller.slopeLimit_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.slopeLimit_nonneg

/-- info: 'Unisono.Solutions.Controller.abs_knotSlope_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_knotSlope_le

/-- info: 'Unisono.Solutions.Controller.knotSlope_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotSlope_between

/-- info: 'Unisono.Solutions.Controller.knotLevelState_concat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelState_concat

/-- info: 'Unisono.Solutions.Controller.knotLevelStep_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelStep_level

/-- info: 'Unisono.Solutions.Controller.foldl_knotLevelStep_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.foldl_knotLevelStep_level

/-- info: 'Unisono.Solutions.Controller.knotLevelState_append_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelState_append_level

/-- info: 'Unisono.Solutions.Controller.knotLevelState_knot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelState_knot

/-- info: 'Unisono.Solutions.Controller.knotLevelStep_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelStep_mem

/-- info: 'Unisono.Solutions.Controller.knotLevelState_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelState_mem

/-- info: 'Unisono.Solutions.Controller.knotLevelState_aim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotLevelState_aim

/-- info: 'Unisono.Solutions.Controller.handoverView_dropLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.handoverView_dropLast

/-- info: 'Unisono.Solutions.Controller.announcedAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announcedAt_eq

/-- info: 'Unisono.Solutions.Controller.announcedAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announcedAt_succ

/-- info: 'Unisono.Solutions.Controller.abs_announcedAt_slope_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_announcedAt_slope_le

/-- info: 'Unisono.Solutions.Controller.knotPeriod_add_slope_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotPeriod_add_slope_pos

/-- info: 'Unisono.Solutions.Controller.knotPeriod_add_slope_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotPeriod_add_slope_le

/-- info: 'Unisono.Solutions.Controller.announcedAt_fst_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announcedAt_fst_mem

/-- info: 'Unisono.Solutions.Controller.announced_eq_announcedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.announced_eq_announcedAt

/-- info: 'Unisono.Solutions.Controller.dueEdge_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueEdge_succ

/-- info: 'Unisono.Solutions.Controller.dueSlope_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueSlope_pos

/-- info: 'Unisono.Solutions.Controller.dueSlope_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueSlope_mem

/-- info: 'Unisono.Solutions.Controller.dueEdge_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueEdge_strictMono

/-- info: 'Unisono.Solutions.Controller.runHeader_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.runHeader_eq

/-- info: 'Unisono.Solutions.Controller.runHeader_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.runHeader_due

/-- info: 'Unisono.Solutions.Controller.covers_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.covers_iff

/-- info: 'Unisono.Solutions.Controller.covers_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.covers_unique

/-- info: 'Unisono.Solutions.Controller.dueOf_eq_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueOf_eq_of_mem

/-- info: 'Unisono.Solutions.Controller.dueAt_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueAt_right

/-- info: 'Unisono.Solutions.Controller.dueAt_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.dueAt_sub_mem

/-- info: 'Unisono.Solutions.Controller.ruled_block_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_block_arrived

/-- info: 'Unisono.Solutions.Controller.runHeader_mem_headersOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.runHeader_mem_headersOf

/-- info: 'Unisono.Solutions.Controller.headersOf_noLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.headersOf_noLoss

/-- info: 'Unisono.Solutions.Controller.arrival_mem_arrivalsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrival_mem_arrivalsOf

/-- info: 'Unisono.Solutions.Controller.mem_arrivalsOf_noLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_arrivalsOf_noLoss

/-- info: 'Unisono.Solutions.Controller.ruled_chosen_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_chosen_iff

/-- info: 'Unisono.Spec.CaptureDevice.exists_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.exists_block

/-- info: 'Unisono.Spec.CaptureDevice.first_le_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.first_le_of_mem

/-- info: 'Unisono.Spec.Follows.none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Follows.none_iff

/-- info: 'Unisono.Solutions.Controller.KnotSetting.handovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.KnotSetting.handovers

/-- info: 'Unisono.Solutions.Controller.KnotSetting.requests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.KnotSetting.requests

/-- info: 'Unisono.Solutions.Controller.ruled_mem_held_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_mem_held_iff

/-- info: 'Unisono.Solutions.Controller.followed_silent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.followed_silent

/-- info: 'Unisono.Solutions.Controller.chosen_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.chosen_eq_some_iff

/-- info: 'Unisono.Solutions.Controller.estimate_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.estimate_sub_mem

/-- info: 'Unisono.Solutions.Controller.abs_chosen_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_chosen_sub_le

/-- info: 'Unisono.Spec.World.knotTime_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotTime_succ

/-- info: 'Unisono.Spec.World.knotTime_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.knotTime_succ_sub

/-- info: 'Unisono.Solutions.Controller.timed_chosen_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_chosen_parts

/-- info: 'Unisono.Solutions.Controller.envelope_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.envelope_add

/-- info: 'Unisono.Solutions.Controller.requestOutput_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.requestOutput_succ

/-- info: 'Unisono.Solutions.Controller.envelopeReading_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.envelopeReading_succ

/-- info: 'Unisono.Solutions.Controller.timed_reading_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_reading_succ

/-- info: 'Unisono.Solutions.Controller.timed_estimate_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_estimate_succ

/-- info: 'Unisono.Solutions.Controller.abs_chosen_succ_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_chosen_succ_sub_le

/-- info: 'Unisono.Solutions.Controller.stepOver_chosen_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.stepOver_chosen_eq_zero

/-- info: 'Unisono.Solutions.Controller.estimateStep_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.estimateStep_mem

/-- info: 'Unisono.Solutions.Controller.chosen_succ_of_settings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.chosen_succ_of_settings

/-- info: 'Unisono.Solutions.Controller.stepOver_eq_zero_of_settings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.stepOver_eq_zero_of_settings

/-- info: 'Unisono.Solutions.Controller.ruled_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ruled_exchange

/-- info: 'Unisono.Solutions.Controller.exchangesOf_append_asked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exchangesOf_append_asked

/-- info: 'Unisono.Solutions.Controller.timed_reading_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_reading_upper

/-- info: 'Unisono.Solutions.Controller.timed_reading_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_reading_lower

/-- info: 'Unisono.Solutions.Controller.timed_chosen_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_chosen_bounds

/-- info: 'Unisono.Solutions.Controller.followed_silent_knot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.followed_silent_knot

/-- info: 'Unisono.Solutions.Controller.timed_silent_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.timed_silent_room

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.isBacklog_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.isBacklog_host

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.handed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.handed_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.arrival_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.arrival_handed

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.reaches_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.reaches_mono

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.blockLength_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.blockLength_eq

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.noLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.noLoss

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.knotSetting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.knotSetting

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.silent_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.silent_reaches

/-- info: 'Unisono.Spec.GenerativeWorld.Builds.silent_late' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.GenerativeWorld.Builds.silent_late

/-- info: 'Unisono.Solutions.Controller.arrivalsOf_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrivalsOf_pairwise

/-- info: 'Unisono.Solutions.Controller.arrivalSlope_eq_of_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrivalSlope_eq_of_pairwise

/-- info: 'Unisono.Solutions.Controller.windowArrivals_eq_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.windowArrivals_eq_filter

/-- info: 'Unisono.Solutions.Controller.mem_windowArrivals_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_windowArrivals_iff

/-- info: 'Unisono.Solutions.Controller.streamDelay_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.streamDelay_pos

/-- info: 'Unisono.Solutions.Controller.queryDelay_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.queryDelay_pos

/-- info: 'Unisono.Solutions.Controller.queryDelay_add_streamDelay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.queryDelay_add_streamDelay

/-- info: 'Unisono.Solutions.Controller.mem_arrivalsOf_of_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.mem_arrivalsOf_of_idle

/-- info: 'Unisono.Solutions.Controller.arrival_mem_arrivalsOf_of_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrival_mem_arrivalsOf_of_idle

/-- info: 'Unisono.Solutions.Controller.arrivalsOf_request_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrivalsOf_request_pairwise

/-- info: 'Unisono.Solutions.Controller.arrivalSlope_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrivalSlope_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.recentExchange_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.recentExchange_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.exists_exchange_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_exchange_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.halfTrip_mem_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.halfTrip_mem_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.out_sub_asked_of_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.out_sub_asked_of_idle

/-- info: 'Unisono.Solutions.Controller.out_sub_asked_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.out_sub_asked_mem

/-- info: 'Unisono.Solutions.Controller.hostReading_out_sub_asked_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.hostReading_out_sub_asked_mem

/-- info: 'Unisono.Solutions.Controller.ratioAt_mem_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ratioAt_mem_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.abs_out_sub_outputAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.abs_out_sub_outputAt_le

/-- info: 'Unisono.Solutions.Controller.drift_mem_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.drift_mem_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.windowArrival_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.windowArrival_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.envelopeReading_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.envelopeReading_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.capture_sub_mem_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.capture_sub_mem_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.knotInput_eq_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knotInput_eq_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.knot_eq_of_undisturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.knot_eq_of_undisturbed

/-- info: 'Unisono.Solutions.Controller.blockCheck_of_knot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.blockCheck_of_knot

/-- info: 'Unisono.Solutions.Controller.exists_dueEdge_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_dueEdge_cover

/-- info: 'Unisono.Solutions.Controller.duePos_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.duePos_eq

/-- info: 'Unisono.Solutions.Controller.duePos_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.duePos_sub_mem

/-- info: 'Unisono.Solutions.Controller.margin_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.margin_mem

/-- info: 'Unisono.Solutions.Controller.plays_eq_of_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.plays_eq_of_margin

/-- info: 'Unisono.Solutions.Controller.plays_of_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.plays_of_delay

/-- info: 'Unisono.Solutions.Controller.exchange_roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exchange_roundTrip

/-- info: 'Unisono.Solutions.Controller.clockLineFrom_of_undelayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.clockLineFrom_of_undelayed

/-- info: 'Unisono.Solutions.Controller.plays_under_pauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.plays_under_pauses

/-- info: 'Unisono.Solutions.Controller.clockLineFrom_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.clockLineFrom_of_exact

/-- info: 'Unisono.Spec.World.PlaysAtLatencies.playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.PlaysAtLatencies.playsOnly

/-- info: 'Unisono.Spec.World.latency_eq_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.latency_eq_of_playsOnly

/-- info: 'Unisono.Spec.World.meanLatency_le_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.meanLatency_le_of_playsOnly

/-- info: 'Unisono.Spec.World.tracking_le_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.tracking_le_of_playsOnly

/-- info: 'Unisono.Spec.World.sync_le_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.sync_le_of_playsOnly

/-- info: 'Unisono.Spec.longRun_le_mul_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.longRun_le_mul_add

/-- info: 'Unisono.Spec.PlaybackDevice.tsum_out_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.tsum_out_lt

/-- info: 'Unisono.Spec.World.accruedOutputs_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.accruedOutputs_eq_sum

/-- info: 'Unisono.Spec.World.longRun_outputs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.longRun_outputs_le

/-- info: 'Unisono.Spec.nextContinuous_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.nextContinuous_gt

/-- info: 'Unisono.Spec.World.speed_eq_one_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.speed_eq_one_of_playsOnly

/-- info: 'Unisono.Spec.World.roughnessCost_eq_zero_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.roughnessCost_eq_zero_of_playsOnly

/-- info: 'Unisono.Spec.World.roughness_eq_zero_of_playsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.roughness_eq_zero_of_playsOnly

/-- info: 'Unisono.Spec.missingAt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missingAt_le_one

/-- info: 'Unisono.Spec.trailing_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.trailing_le

/-- info: 'Unisono.Spec.trailing_succ_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.trailing_succ_none

/-- info: 'Unisono.Spec.trailing_succ_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.trailing_succ_some

/-- info: 'Unisono.Spec.isSome_before_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.isSome_before_trailing

/-- info: 'Unisono.Spec.gapBefore_le_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.gapBefore_le_trailing

/-- info: 'Unisono.Spec.sum_gapBefore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_gapBefore_le

/-- info: 'Unisono.Spec.toNat_cast_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.toNat_cast_le

/-- info: 'Unisono.Spec.missedAt_le_of_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_le_of_line

/-- info: 'Unisono.Spec.exists_missedAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_missedAt_le

/-- info: 'Unisono.Spec.sum_missedAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_missedAt_le

/-- info: 'Unisono.Spec.discontinuityAt_le_of_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.discontinuityAt_le_of_line

/-- info: 'Unisono.Spec.sum_discontinuityAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_discontinuityAt_le

/-- info: 'Unisono.Spec.World.missed_le_of_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.missed_le_of_line

/-- info: 'Unisono.Spec.World.discontinuities_le_of_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.discontinuities_le_of_line

/-- info: 'Unisono.Spec.longRun_le_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.longRun_le_of_tendsto

/-- info: 'Unisono.Spec.PlaybackDevice.find_le_of_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.find_le_of_line

/-- info: 'Unisono.Spec.World.longRun_outputs_le_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.longRun_outputs_le_rate

/-- info: 'Unisono.Spec.World.discontinuities_le_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.discontinuities_le_outputs

/-- info: 'Unisono.Spec.missedAt_le_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.missedAt_le_of_slope

/-- info: 'Unisono.Spec.exists_missedAt_le_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_missedAt_le_of_slope

/-- info: 'Unisono.Spec.sum_missedAt_le_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.sum_missedAt_le_of_slope

/-- info: 'Unisono.Spec.World.missed_le_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.missed_le_of_slope

/-- info: 'Unisono.Solutions.Controller.exists_duePosition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_duePosition_nonneg

/-- info: 'Unisono.Solutions.Controller.lateRate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lateRate_le

/-- info: 'Unisono.Solutions.Controller.cost_le_of_heldLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_of_heldLevel

/-- info: 'Unisono.Solutions.Controller.cost_le_under_pauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_under_pauses

/-- info: 'Unisono.Solutions.Controller.duePosition_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.duePosition_eq

/-- info: 'Unisono.Solutions.Controller.cost_le_of_duePositions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_of_duePositions

/-- info: 'Unisono.Solutions.Controller.cost_le_of_plays_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_of_plays_margin

/-- info: 'Unisono.Solutions.Controller.cost_le_outputs_of_plays_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_outputs_of_plays_due

/-- info: 'Unisono.Solutions.Controller.exists_plays_heldLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_plays_heldLevel

/-- info: 'Unisono.Solutions.Controller.cost_le_outputs_of_heldLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_outputs_of_heldLevel

/-- info: 'Unisono.Solutions.Controller.cost_le_outputs_under_pauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_le_outputs_under_pauses

/-- info: 'Unisono.Solutions.FixedDelay.exists_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exists_query

/-- info: 'Unisono.Solutions.FixedDelay.exchange_of_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exchange_of_query

/-- info: 'Unisono.Solutions.FixedDelay.exchange_of_query_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.FixedDelay.exchange_of_query_before

/-- info: 'Unisono.Solutions.Controller.arrival_of_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.arrival_of_idle

/-- info: 'Unisono.Solutions.Controller.asked_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.asked_succ_sub

/-- info: 'Unisono.Solutions.Controller.exists_asked_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_asked_between

/-- info: 'Unisono.Solutions.Controller.exists_undelayed_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_undelayed_exchange

/-- info: 'Unisono.Solutions.Controller.exists_twoUndelayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_twoUndelayed

/-- info: 'Unisono.Solutions.Controller.ae_twoUndelayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ae_twoUndelayed

/-- info: 'Unisono.Solutions.Controller.ae_cost_le_heldLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ae_cost_le_heldLevel

/-- info: 'Unisono.Solutions.Controller.prior_paused_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.prior_paused_monotone

/-- info: 'Unisono.Solutions.Controller.prior_paused_rightContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.prior_paused_rightContinuous

/-- info: 'Unisono.Solutions.Controller.blockDelay_eq_arrivalM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.blockDelay_eq_arrivalM

/-- info: 'Unisono.Solutions.Controller.measurable_blockTimes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.measurable_blockTimes

/-- info: 'Unisono.Solutions.Controller.blockTimes_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.blockTimes_scalars

/-- info: 'Unisono.Solutions.Controller.ae_tendsto_slowBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ae_tendsto_slowBlocks

/-- info: 'Unisono.Solutions.Controller.tendsto_sum_ceil_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.tendsto_sum_ceil_div

/-- info: 'Unisono.Solutions.Controller.card_le_of_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.card_le_of_line

/-- info: 'Unisono.Solutions.Controller.neededBlock_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.neededBlock_mem

/-- info: 'Unisono.Solutions.Controller.slowAt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.slowAt_le_one

/-- info: 'Unisono.Solutions.Controller.sum_slowAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.sum_slowAt_le

/-- info: 'Unisono.Solutions.Controller.longRun_slowAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.longRun_slowAt_le

/-- info: 'Unisono.Solutions.Controller.lateRate_le_of_slowBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lateRate_le_of_slowBlocks

/-- info: 'Unisono.Solutions.Controller.ae_lateRate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ae_lateRate_le

/-- info: 'Unisono.Solutions.Controller.sub_one_le_rateExcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.sub_one_le_rateExcess

/-- info: 'Unisono.Solutions.Controller.ae_cost_le_heldLevelCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ae_cost_le_heldLevelCost

/-- info: 'Unisono.Solutions.Controller.expectedCost_le_heldLevelCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.expectedCost_le_heldLevelCost

/-- info: 'Unisono.Solutions.Controller.average_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.average_le

/-- info: 'Unisono.Solutions.Controller.pairAverage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.pairAverage_le

/-- info: 'Unisono.Solutions.Controller.le_rpow_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.le_rpow_third

/-- info: 'Unisono.Solutions.Controller.lateProbability_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lateProbability_mem

/-- info: 'Unisono.Solutions.Controller.exists_latencyCosts_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_latencyCosts_add_le

/-- info: 'Unisono.Solutions.Controller.exists_heldLevelCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.exists_heldLevelCost_le

/-- info: 'Unisono.Solutions.Controller.lintegral_lt_top_of_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lintegral_lt_top_of_le_exp

/-- info: 'Unisono.Solutions.Controller.lintegral_heldLevelCost_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lintegral_heldLevelCost_lt_top

/-- info: 'Unisono.Solutions.Controller.expectedCost_heldLevel_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.expectedCost_heldLevel_lt_top

/-- info: 'Unisono.Solutions.Controller.limited_withinStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.limited_withinStep

/-- info: 'Unisono.Solutions.Controller.limited_plays_eq_heldLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.limited_plays_eq_heldLevel

/-- info: 'Unisono.Solutions.Controller.cost_limited_le_of_heldLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_limited_le_of_heldLevel

/-- info: 'Unisono.Solutions.Controller.cost_limited_le_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.cost_limited_le_outputs

/-- info: 'Unisono.Solutions.Controller.ae_cost_le_limitedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.ae_cost_le_limitedCost

/-- info: 'Unisono.Solutions.Controller.expectedCost_le_limitedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.expectedCost_le_limitedCost

/-- info: 'Unisono.Solutions.Controller.lintegral_limitedCost_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.lintegral_limitedCost_lt_top

/-- info: 'Unisono.Solutions.Controller.expectedCost_limited_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Solutions.Controller.expectedCost_limited_lt_top

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

/-- info: 'Unisono.Spec.Network.after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Network.after

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

/-- info: 'Unisono.Spec.World.WithinBounds.asked_lt_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.WithinBounds.asked_lt_out

/-- info: 'Unisono.Spec.World.WithinBounds.asked_lt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.World.WithinBounds.asked_lt_of_le

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

/-- info: 'Unisono.Spec.Solution.plays_of_asked_step_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_of_asked_step_of_lt

/-- info: 'Unisono.Spec.Solution.plays_eq_none_of_out_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.plays_eq_none_of_out_le

/-- info: 'Unisono.Spec.Solution.asked_lt_out_of_plays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.Solution.asked_lt_out_of_plays

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

/-- info: 'Unisono.Spec.PlaybackDevice.block_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.PlaybackDevice.block_injective

/-- info: 'Unisono.Spec.CaptureDevice.block_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.CaptureDevice.block_injective

/-- info: 'Unisono.Spec.tiedCount_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.tiedCount_of_ne

/-- info: 'Unisono.Spec.tiedCount_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.tiedCount_succ

/-- info: 'Unisono.Spec.exists_ne_of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.exists_ne_of_monotone

/-- info: 'Unisono.Spec.tiedCount_add_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.tiedCount_add_right

/-- info: 'Unisono.Spec.remHandedFrom_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remHandedFrom_of_ne

/-- info: 'Unisono.Spec.remHandedFrom_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remHandedFrom_cons

/-- info: 'Unisono.Spec.remAskedFrom_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remAskedFrom_of_ne

/-- info: 'Unisono.Spec.remAskedFrom_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remAskedFrom_cons

/-- info: 'Unisono.Spec.remHanded_sender' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remHanded_sender

/-- info: 'Unisono.Spec.remHanded_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remHanded_of_ne

/-- info: 'Unisono.Spec.remAsked_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remAsked_eq_nil

/-- info: 'Unisono.Spec.remAsked_update_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remAsked_update_cons

/-- info: 'Unisono.Spec.remAsked_update_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.remAsked_update_of_ne

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

/-- info: 'Unisono.Analysis.single_law_minimizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.single_law_minimizes

/-- info: 'Unisono.Analysis.single_law_unique_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.single_law_unique_ae

/-- info: 'Unisono.Analysis.multiCycleCost_modal_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multiCycleCost_modal_split

/-- info: 'Unisono.Analysis.multi_lipsync_minimizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_minimizes

/-- info: 'Unisono.Analysis.multi_lipsync_unique_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_unique_ae

/-- info: 'Unisono.Analysis.multi_lipsync_cost_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_cost_rate

/-- info: 'Unisono.Analysis.multi_lipsync_law_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lipsync_law_cost_le

/-- info: 'Unisono.Analysis.multi_lowlatency_minimizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lowlatency_minimizes

/-- info: 'Unisono.Analysis.multi_lowlatency_unique_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.multi_lowlatency_unique_ae

/-- info: 'Unisono.Analysis.decentralized_star_cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.decentralized_star_cost_eq

/-- info: 'Unisono.Analysis.symmetric_star_cost_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.symmetric_star_cost_split

/-- info: 'Unisono.Analysis.decentralized_star_uncorrelated_minimizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.decentralized_star_uncorrelated_minimizes

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

/-- info: 'Unisono.Analysis.thomson_blue_least_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Analysis.thomson_blue_least_variance

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

/-- info: 'Unisono.Spec.ForwardStar.isStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Unisono.Spec.ForwardStar.isStar

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
