# The theorems

What is proved, by what it says about the program. Every theorem named here
is in `lean/Unisono`, and `lean/Unisono/Audit.lean` lists each with the
axioms its proof uses, which are the three standard ones of Lean with
classical logic. The build fails if a proof has a gap or a list changes.

There are two kinds. Theorems under `Unisono.Model` are about the problem:
real numbers, probabilities, no code. They say what the best estimate, the
best law for the pace and the best level are, under assumptions that
`docs/model.md` states and lists in its last section. All other theorems are
about the code: about the Lean translation of `crates/unisono-core`, which is
regenerated and compared with the Rust on every check (see the README). The
runtime, the signal processing and the program are outside the core and are
tested, not proved.

"Returns for every input" below means: the function ends, and nothing in it
overflows, indexes out of range or otherwise fails, for every state and
every argument, whether or not they could arise in a run.

## 1. The problem

### 1.1 Clocks and their estimate (`Model.Exchange`, `Model.SupportLine`, `Model.LineFit`)

| Theorem | What it says |
|---|---|
| `Exchange.error_bound` | An exchange of packets in both directions gives the offset of two clocks up to half the difference of the smallest delays, which nothing reveals, and half the excess of the two delays. |
| `SupportLine.highest`, `estimate_isGreatest` | The line through two samples on either side of a time, under all samples, is the highest there of all lines under the samples: the least estimate that is never below a relation the samples allow. |
| `SupportLine.excess_le`, `excess_near` | At the mean of the sample times that line is also the one the samples lie above by the least, added up: the most likely line for delays that are independent and exponential. Rounding the mean costs at most the number of samples times the difference of two slopes times the rounding. |
| `SupportLine.error_at_centre`, `error_ahead` | The error of that line where it is highest, and after the newest sample where a schedule needs it, from bounds on the clocks and on two samples only. Delayed packets do not enter. |
| `LineFit.cost_le`, `error_bound` | The line computed from weighted sums has the least weighted sum of squared residuals, and its error is bounded when the errors of the points are. |
| `LineFit.schedule_invariant` | Synchronization does not depend on the offset or the rate of the sender's clock. |

### 1.2 The stream (`Model.Stream`)

| Theorem | What it says |
|---|---|
| `group_misses_iff` | The group of receivers misses a frame exactly when the level is below the largest need over the receivers. |
| `sum_sq_errors` | The squared timing errors are the squared distances from their mean, which is receivers out of step, plus the squared mean for each, which is latency. |
| `dueTime_position` | The position that is due at a time, from what a packet says of its first frame and of the frames after it. |
| `groupNeed_errors`, `group_misses_errors` | Timing errors within a bound move the need of the group by no more than the bound, so the level and the paces can be chosen apart up to that. |

### 1.3 The pace (`Model.Regulation`, `Model.RegulationRandom`, `Model.Gains`)

The problem: before each cycle of its device a receiver knows how far it is
behind the schedule and at what pace it reads; it chooses the change of its
pace; a cycle costs the weighted squared distance plus the squared change.

| Theorem | What it says |
|---|---|
| `cost_add_value` | The cost of a cycle plus the value after it is the value before it plus a multiple of the squared distance of the change of pace from the law. Everything below follows from this. |
| `total_cost_ge`, `total_cost_law` | Without revisions of the schedule: no sequence of changes of the pace costs less than the value of the starting state, and the law costs exactly that. |
| `value_step`, `distance_from_rest` | Under the law each cycle multiplies the value by the same factor below one, and a distance from rest shrinks at that rate. |
| `weight_gainFor`, `gain_unique` | The law in closed form for a given weight, and that it is the only one. |
| `mean_cost_sum`, `mean_cost_law_le` | With revisions that cannot be foreseen and nothing else assumed about them: among all ways of playing that use only what is known before each cycle, the law has the least mean cost, for every number of cycles. |
| `mean_value_law_le`, `mean_cost_rate` | Under the law the mean cost per cycle stays bounded by the mean value of a revision, and no way of playing has a smaller mean cost per cycle in the long run. |
| `mean_square_split`, `unforeseen_revision` | The distance to the true schedule is the distance to the best estimate of it plus that estimate's error, which no way of playing changes; and a revision of a best estimate cannot be foreseen. |
| `distance_step`, `unforeseen_pace` | The distance to the estimated schedule obeys the equation of the problem, and the revision of the expected advance cannot be foreseen when the true pace is expected to stay. |
| `at_limit`, `next_shift` | How the law behaves at the limit of the pace, and around a pace that differs from the schedule's. |
| `Gains.gains_close`, `gains_of_integers`, `law_close` | The gains computed in whole numbers, with every division and root rounded down, are within stated bounds of the gains of the law, and so is what a cycle is planned to read. |
| `Gains.planned`, `cost_of_distance` | What the law has a cycle read, and what a distance from the law costs: its square over the square of the law's modulus. |

### 1.4 The level (`Model.Level`)

| Theorem | What it says |
|---|---|
| `measure_largest`, `measure_largest_le` | When nothing sets the next stretch apart from the stretches seen, it needs strictly more than all of them with probability at most one in their number and one (`measure_largest_le`), and with equality when ties have probability zero (`measure_largest`), whatever the law of the needs. |
| `integral_predictive` | The mean cost of the next stretch, under the law that the choice takes. |
| `volume_missed`, `missed_le`, `missed_ge` | The time for which a stretch is missed at a level, for a pause that holds packets back: the count used never understates it, and overstates it by at most the time from the start of the stretch to the start of the pause. |
| `volume_lasts`, `move_pays_iff` | When the present is as likely in any part of the time over which the needs keep their law, a move of the level more likely than not pays for itself exactly when what it saves over the time of the evidence exceeds its cost. |

## 2. The code

### 2.1 Arithmetic (`Fixed`)

| Theorem | What it says |
|---|---|
| `saturate_spec`, `mul_shift_spec`, `div_floor_spec`, `div_floor_wide_spec`, `rem_euclid_wide_spec` | Saturation, a rounded product, division rounded down, and Euclidean remainder return the stated numbers (with `none` for remainder modulo zero). |
| `root_spec` | The square root returns the largest whole number whose square is at most its argument. |

### 2.2 Packets (`Packet`)

| Theorem | What it says |
|---|---|
| `audio_roundtrip`, `report_roundtrip`, `echo_roundtrip`, `request_roundtrip` | A header that is written and read back is the same header. |
| `write_audio_spec`, `write_report_spec`, `write_echo_spec`, `write_request_spec` | The exact bytes, returned lengths, and report padding zeros of each kind of packet. |
| `parse_audio_valid`, `validate_audio_spec`, `payload_spec` | A header that is accepted is a valid one, with a payload of exactly the length the header says. |
| `kind_spec`, `parse_audio_kind`, `parse_report_kind`, `parse_echo_kind`, `parse_request_kind` | A packet is read as one kind only. |
| `read_spec`, `write_spec` | Reading and writing a number of up to eight bytes at a place. |
| `parse_audio_total`, `write_audio_total`, `parse_report_total`, `write_report_total`, `parse_echo_total`, `write_echo_total`, `parse_request_total`, `write_request_total`, `parse_needs_total`, `write_needs_total` | Reading and writing return for every input: no bytes from the network can make a parser fail. |

### 2.3 The clock estimate (`Relation`, `Estimate`)

| Theorem | What it says |
|---|---|
| `fit_spec` | The fit changes nothing but the line, and a line it stores passes through a kept sample with no kept sample below it and its slope within `limit`. It is the line through two kept samples around the mean of their times, or its slope is at the limit over one second. |
| `mean_time_spec`, `anchor_near_mean` | That mean, rounded down to a nanosecond. |
| `through_best`, `through_excess` | Read in real numbers, the stored line is the best line of section 1.1: the highest at the mean of the times, and the most likely one up to the rounding. |
| `side_spec`, `is_under_spec`, `bridge_spec`, `slope_within_spec`, `limited_spec`, `eval_spec` | The parts of the fit and line evaluation: the side of a line a sample lies on, whether a line is under all kept samples, the two samples the line is drawn through, the exact slope-bound test, the line at the slope limit, and exact clamped line evaluation. |
| `put_spec`, `drop_oldest_spec`, `forget_before_spec`, `append_spec`, `keep_spec`, `end_window_spec`, `new_spec`, `remember_spec`, `reset_window_spec`, `consider_spec`, `overtaken_spec` | Keeping, bounding, and forgetting samples change what they say and nothing else, preserving the kept-count bound `len ≤ M`. |
| `observe_spec`, `observe_later`, `observe_in_order` | From any state: a sample that can come from an overtaken packet leaves the estimator exactly as it is, and every other one is taken in. So an estimator takes a stream in again within the time it remembers, whatever it held. |
| `observe_total`, `end_window_total` | Taking in a packet and ending a window return for every input. |

### 2.4 A device's line (`Device`)

| Theorem | What it says |
|---|---|
| `fit_spec`, `when_spec`, `when_cycle_spec` | Fitting sums/spread/tilt, when a frame leaves the device, and how long a cycle takes: no sum or product wraps, and the result is the stated function of the kept reports. |
| `beyondZ_eq_floor_lineFit`, `beyondSlopeQ16Z_eq_floor_lineFit` | That function is the least-squares line of section 1.1 through the reports, rounded down. |
| `observe_spec`, `observe_after_aside`, `step_spec` | A report is kept, or set aside with everything else as it was, and that only when nothing was set aside before: of two reports in a row the second is kept, so the line follows the device again from any state. |
| `push_spec`, `start_spec`, `shift_spec` | Keeping a report, starting anew (keeping only the new report with `len = 1` when `W > 0`), and shifting every kept report's timestamp while preserving positions and unkept slots. |
| `observe_total`, `when_total` | Both return for every input. |

### 2.5 The frames a receiver holds (`Presence`)

| Theorem | What it says |
|---|---|
| `mark_spec`, `mark_frame_spec`, `countOf_total` | After a packet arrives, a frame is held exactly when it was held before or the packet brought it, and each frame of the packet has exactly one outcome. |
| `Arrived.comm`, `Arrived.again` | Two packets leave the same frames held in whichever order they arrive, and a packet that arrives twice changes nothing. |
| `advance_spec`, `run_spec`, `gap_spec`, `held_spec`, `new_spec`, `restart_spec`, `width_spec`, `covers_spec` | Moving the start of what is held, counting held and missing frames in a row, and starting anew. |

### 2.6 The receiver (`Receiver`)

| Theorem | What it says |
|---|---|
| `packet_spec` | What a receiver does with a packet, in every case: another stream's is ignored; a timeline is taken up, kept, or a stray one remembered for a second packet to confirm. |
| `follows_after_silence`, `late_run_is_short`, `restart_stores` | From any state, a receiver sent packets of one timeline follows it within the set time of silence, and holds the packet it starts anew at. |
| `wrong_stream_packet_noop`, `wrong_stream_echo_noop`, `single_stray_timeline_noop` | Packets of another stream, and one stray packet of another timeline, leave playback, schedule, clock estimate, path delay, answers, and report departures unchanged. |
| `take_spec`, `take_idle`, `skip_spec` | The run of frames handed to the device is all held or all missing, starts at the playhead, and the playhead never moves back. |
| `cycle_spec`, `due_at_total` | Planning a cycle returns for every state and reading of the clock and changes only the schedules and the regulator. |
| `echo_spec`, `report_spec`, `reported_spec` | Measuring the delay of the path changes nothing about the timeline or the frames held. |
| `adopt_spec`, `keep_newest_spec`, `new_spec` | Taking up a timeline (preserving path answers and report departures on the same clock, and clearing them on a new clock), moving to the newest frames, and a new receiver. |

### 2.7 The regulator and timing (`Player`, `Gains`, `Due`)

| Theorem | What it says |
|---|---|
| `cycle_spec`, `cycle_step_small`, `step_clamped_spec` | Planning a cycle returns for every state and schedule, and its step is within the limit of the pace, which is a step the resampler takes. |
| `gain_spec`, `gains_spec`, `regulate_spec` | The gain of a cycle, and that the two gains the code computes and what it has the cycle read are within stated bounds of the best law's (section 1.3). |
| `Due.due_spec`, `Due.dueUnits_eq_floor` | `timing::due` returns `none` if and only if rate, pace, or stretch is non-positive or the frame falls outside `[0, 2⁶⁴)`, and otherwise returns the exact position from section 1.2 rounded down to `2⁻³²` frame. |
| `sender_time_total`, `due_total`, `position_units_total`, `position_from_units_total`, `step_units_total`, `step_new_total`, `position_advance_total`, `step_from_parts_per_billion_total` | The conversions between times, positions and steps return for every input. |

### 2.8 The sender (`Sender`)

| Theorem | What it says |
|---|---|
| `packet_spec` | The packets of a timeline follow each other without a break, each with the level and slope in force. |
| `current_level_spec`, `levelAt_eq_floor`, `packet_ramp_consistent`, `level_spec` | The level along a ramp is the exact ramp rounded down, with no rounding that adds up from packet to packet. |
| `restart_spec`, `departed_spec`, `answer_spec` | A restart begins a timeline with a larger number and keeps the level; departures and answers change nothing else. |

### 2.9 Needs, answers and arrivals (`Needs`, `Answers`, `Arrivals`)

| Theorem | What it says |
|---|---|
| `Needs.observe_total`, `recent_total`, `new_total`, `clear_total`, `newest_total`, `get_total` | Keeping the largest need of each stretch returns for every input. |
| `Answers.observe_total`, `shortest_total`, `new_total`, `clear_spec` | Keeping the answers with the shortest time there and back returns for every input, and `clear` marks every slot empty. |
| `Arrivals.find_spec`, `record_spec` | The table of arrival times keeps the first arrival of each report and finds it. |

### 2.10 How long loops run (`Rounds`)

| Theorem | What it says |
|---|---|
| `endsWithin_of_measure` | A loop whose every round lowers a number that cannot go below zero ends within that many rounds. |
| `mark_rounds`, `run_rounds`, `gap_rounds`, `advance_rounds`, `clear_rounds`, `find_rounds`, `sums_rounds`, `shift_rounds` | The loops on the audio thread take at most one round for each frame, word, arrival or report they go through. |

## 3. What is not proved

`docs/model.md` marks each such point where it arises, with the words "not
stated in Lean". The main ones: the estimators are not derived as the best
estimates that section 1.3 asks for, and what that costs is measured, not
bounded; that the fit always finds a line; the rounding of a cycle's step;
and everything outside the core, where the search for the level, the
resampler and the concealment are floating-point code that is tested.
