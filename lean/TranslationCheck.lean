/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
import UnisonoCore

/-!
# Comparison of the translation with the Rust it came from

Reads the lines that the `translation-check` program prints, evaluates the
translated function on the inputs of each line and compares the result with
the one the Rust computed. Run it with `lean --run`.
-/

open Aeneas Aeneas.Std unisono_core

/-- The signed machine integer with the two's complement bits of `x`. -/
def signed (ty : IScalarTy) (x : Int) : IScalar ty := ⟨BitVec.ofInt ty.numBits x⟩

/-- The unsigned machine integer with the low bits of `x`. -/
def unsigned (ty : UScalarTy) (x : Int) : UScalar ty := ⟨BitVec.ofInt ty.numBits x⟩

/-- Feeds packets, each a window, a time and a value, to an estimator that
remembers eight samples, and returns whether it has a line, the line and the
number of samples it keeps. -/
def runRelation (span limit : Int) (packets : List (Int × Int × Int)) :
    Result (List Int) := do
  let start ← relation.Estimator.new 8#usize (signed .I64 span) (signed .I64 limit)
  let fed ← packets.foldlM
    (fun estimator (window, time, value) =>
      relation.Estimator.observe estimator (unsigned .U64 window)
        ⟨signed .I64 time, signed .I64 value⟩)
    start
  let ended ← relation.Estimator.end_window fed
  let line ← relation.Estimator.impl.line ended
  let kept ← relation.Estimator.impl.kept ended
  match line with
  | some l => pure [1, l.time.val, l.value.val, l.rise.val, l.run.val, kept.val]
  | none => pure [0, 0, 0, 0, 0, kept.val]

/-- Groups a flat list into triples; `none` if its length is not a multiple of three. -/
def triples : List Int → Option (List (Int × Int × Int))
  | [] => some []
  | a :: b :: c :: rest => (triples rest).map ((a, b, c) :: ·)
  | _ => none

/-- A slice of bytes with the given values. -/
def byteSlice (values : List Int) : Slice Std.U8 :=
  let bytes := values.map (unsigned .U8)
  if h : bytes.length ≤ Usize.max then Slice.from bytes h else Slice.from [] (by simp)

/-- The fields of a header as numbers, in the order of the layout. -/
def headerFields (h : packet.Audio) : List Int :=
  [h.stream.val, h.timeline.val, h.index.val, h.capture.val, h.rate.val, h.frames.val,
    h.channels.val,
    (match h.format with
      | .Signed16 => 1
      | .Signed24 => 2),
    h.level.val, h.level_slope.val, h.span.val, h.window.val, h.flags.val, h.protection.val,
    h.stamped_index.val, h.stamped_departure.val, h.drift.val]

/-- A reason for rejection as two numbers: which reason, and its detail. -/
def rejection : packet.Rejected → List Int
  | .TooShort => [1, 0]
  | .NotUnisono => [2, 0]
  | .Version v => [3, v.val]
  | .Kind k => [4, k.val]
  | .Format f => [5, f.val]
  | .Length => [6, 0]

/-- What parsing gives, as numbers: 0 and the fields, or the number of the
reason for rejection, its detail, and zeros. -/
def runParse (values : List Int) : Result (List Int) := do
  let parsed ← packet.parse_audio (byteSlice values)
  match parsed with
  | .Ok header => pure (0 :: headerFields header)
  | .Err reason => pure (rejection reason ++ List.replicate 16 0)

/-- Writes a header given by its fields into 256 zero bytes, and returns the
length that writing reports and the first 84 bytes. -/
def runWrite (f : List Int) : Result (List Int) := do
  match f with
  | [stream, timeline, index, capture, rate, frames, channels, format, level, slope, span,
      window, flags, protection, stampedIndex, stampedDeparture, drift] =>
    let header : packet.Audio := {
      stream := unsigned .U16 stream, timeline := unsigned .U64 timeline,
      index := unsigned .U64 index, capture := signed .I64 capture,
      rate := unsigned .U32 rate, frames := unsigned .U16 frames,
      channels := unsigned .U8 channels,
      format := if format = 1 then .Signed16 else .Signed24,
      level := signed .I64 level, level_slope := signed .I32 slope,
      span := unsigned .U32 span, window := unsigned .U32 window,
      flags := unsigned .U16 flags, protection := unsigned .U16 protection,
      stamped_index := unsigned .U64 stampedIndex,
      stamped_departure := signed .I64 stampedDeparture,
      drift := signed .I32 drift }
    let (length, bytes) ← packet.write_audio header (byteSlice (List.replicate 256 0))
    match length with
    | some n => pure (n.val :: (bytes.val.take 84).map (·.val))
    | none => pure [-1]
  | _ => pure [-2]

/-- Applies operations, each three numbers, to a stretch of 192 indices, and
collects their results; see `presence_cases` in the Rust program. -/
def presenceStep (state : presence.Presence 3#usize × List Int) (operation : Int × Int × Int) :
    Result (presence.Presence 3#usize × List Int) := do
  let p := state.1
  let results := state.2
  let a := operation.2.1
  let b := operation.2.2
  if operation.1 = 0 then
    let marked ← presence.Presence.mark p (unsigned .U64 a) (unsigned .U32 b)
    pure (marked.2, results ++ ([marked.1.stored.val, marked.1.duplicate.val,
      marked.1.late.val, marked.1.early.val] : List Int))
  else if operation.1 = 1 then
    let p1 ← presence.Presence.advance p (unsigned .U64 a)
    let base ← presence.Presence.impl.base p1
    pure (p1, results ++ ([base.val] : List Int))
  else if operation.1 = 2 then
    let held ← presence.Presence.held p (unsigned .U64 a)
    pure (p, results ++ [if held then 1 else 0])
  else
    let count ← presence.Presence.run p (unsigned .U64 a) (unsigned .U32 b)
    pure (p, results ++ ([count.val] : List Int))

def runPresence (operations : List (Int × Int × Int)) : Result (List Int) := do
  let start ← presence.Presence.new 3#usize
  let final ← operations.foldlM presenceStep (start, [])
  pure final.2

/-- Groups a flat list into groups of `n`; `none` if its length is not a
multiple of `n`. -/
def groups (n : Nat) (values : List Int) : Option (List (List Int)) :=
  if n = 0 ∨ values.length % n ≠ 0 then none
  else some ((List.range (values.length / n)).map (fun k => (values.drop (k * n)).take n))

/-- The header that the receiver cases use; see `stream_header` in the Rust
program. -/
def streamHeader (timeline index frames flags stampedIndex stampedDeparture : Int) :
    packet.Audio :=
  { stream := 1#u16, timeline := unsigned .U64 timeline, index := unsigned .U64 index,
    capture := signed .I64 (index * 20833), drift := 0#i32, rate := 48000#u32, frames := unsigned .U16 frames,
    channels := 2#u8, format := .Signed16, level := 0#i64, level_slope := 0#i32,
    span := 20#u32, window := 50#u32, flags := unsigned .U16 flags, protection := 0#u16,
    stamped_index := unsigned .U64 stampedIndex,
    stamped_departure := signed .I64 stampedDeparture }

abbrev CheckedReceiver := receiver.Receiver 2#usize 4#usize 2#usize

/-- A plan as numbers: its frames, the frame and fraction of its start, its
step and whether it jumped. -/
def planNumbers (plan : player.Plan) : List Int :=
  [plan.frames.val, plan.start.frame.val, plan.start.fraction.val, plan.step.val,
    if plan.jumped then 1 else 0]

/-- Applies one cycle of six numbers to a regulator and collects the plan;
see `player_cases` in the Rust program. -/
def playerStep (state : player.Player × List Int) (cycle : List Int) :
    Result (player.Player × List Int) :=
  match cycle with
  | [frame, fraction, laterFrame, laterFraction, frames, duration] => do
    let out ← player.Player.cycle state.1
      { frame := unsigned .U64 frame, fraction := unsigned .U64 fraction }
      { frame := unsigned .U64 laterFrame, fraction := unsigned .U64 laterFraction }
      (unsigned .U32 frames) (signed .I64 duration)
    pure (out.2, state.2 ++ planNumbers out.1)
  | _ => pure (state.1, state.2 ++ [-2])

def runPlayer (gain limit jump : Int) (cycles : List (List Int)) : Result (List Int) := do
  let start ← player.Player.new
    { gain := unsigned .U32 gain, limit := unsigned .U32 limit, jump := unsigned .U32 jump }
  let final ← cycles.foldlM playerStep (start, [])
  pure final.2

/-- A truth value as a number. -/
def bit (b : Bool) : Int := if b then 1 else 0

/-- Applies one operation of eight numbers to a receiver and collects its
results; see `receiver_cases` in the Rust program. -/
def receiverStep (state : CheckedReceiver × List Int) (operation : List Int) :
    Result (CheckedReceiver × List Int) := do
  let r := state.1
  let (r1, results) ← (match operation with
    | [0, timeline, index, frames, flags, stampedIndex, stampedDeparture, arrival] => do
      let out ← receiver.Receiver.packet r
        (streamHeader timeline index frames flags stampedIndex stampedDeparture)
        (signed .I64 arrival)
      pure (out.2, ([bit out.1.ignored, bit out.1.adopted, bit out.1.restarted,
        out.1.marked.stored.val,
        out.1.marked.duplicate.val, out.1.marked.late.val, out.1.marked.early.val] : List Int))
    | [1, limit, _, _, _, _, _, _] => do
      let out ← receiver.Receiver.take r (unsigned .U32 limit)
      pure (out.2, ([out.1.first.val, out.1.frames.val, bit out.1.held] : List Int))
    | [2, target, _, _, _, _, _, _] => do
      let out ← receiver.Receiver.skip r (unsigned .U64 target)
      pure (out.2, ([out.1.val] : List Int))
    | [3, time, frames, _, _, _, _, _] => do
      let out ← receiver.Receiver.cycle r (signed .I64 time) (signed .I64 (frames * 20833))
        (unsigned .U32 frames)
      pure (out.2, planNumbers out.1)
    | _ => pure (r, [-2]) : Result (CheckedReceiver × List Int))
  let timeline ← receiver.Receiver.impl.timeline r1
  let playhead ← receiver.Receiver.playhead r1
  let followed : Int := match timeline with
    | some t => t.val
    | none => -1
  pure (r1, state.2 ++ results ++ [followed, playhead.val])

def runReceiver (silence : Int) (operations : List (List Int)) : Result (List Int) := do
  let regulation : player.Regulation :=
    { gain := 262144#u32, limit := 1000000#u32, jump := 30#u32 }
  let start ← receiver.Receiver.new 2#usize 4#usize 2#usize (signed .I64 silence) 200000#i64
    regulation
  let final ← operations.foldlM receiverStep (start, [])
  let line ← receiver.Receiver.impl.clock final.1
  let schedule ← receiver.Receiver.impl.schedule final.1
  let lineNumbers : List Int := match line with
    | some l => [l.time.val, l.value.val, l.rise.val, l.run.val]
    | none => [0, 0, 0, 0]
  let scheduled : Int := match schedule with
    | some s => s.index.val
    | none => -1
  pure (final.2 ++ lineNumbers ++ [scheduled])

/-- Applies one operation of four numbers to a sender and collects its
results; see `sender_cases` in the Rust program. -/
def senderStep (state : sender.Sender × List Int) (operation : List Int) :
    Result (sender.Sender × List Int) := do
  let s := state.1
  let (s1, results) ← (match operation with
    | [0, frames, capture, drift] => do
      let out ← sender.Sender.packet s (unsigned .U16 frames) (signed .I64 capture)
        (signed .I32 drift)
      pure (out.2, ([out.1.index.val, out.1.flags.val, out.1.stamped_index.val,
        out.1.stamped_departure.val, out.1.capture.val, out.1.drift.val] : List Int))
    | [1, timeline, index, departure] => do
      let s1 ← sender.Sender.departed s (unsigned .U64 timeline) (unsigned .U64 index)
        (signed .I64 departure)
      pure (s1, [])
    | [2, timeline, _, _] => do
      let s1 ← sender.Sender.restart s (unsigned .U64 timeline)
      pure (s1, [])
    | _ => pure (s, [-2]) : Result (sender.Sender × List Int))
  let timeline ← sender.Sender.impl.timeline s1
  let next ← sender.Sender.impl.next s1
  pure (s1, state.2 ++ results ++ ([timeline.val, next.val] : List Int))

def runSender (first : Int) (operations : List (List Int)) : Result (List Int) := do
  let settings : sender.Settings :=
    { stream := 1#u16, rate := 48000#u32, channels := 2#u8, format := .Signed16,
      span := 20#u32, window := 50#u32 }
  let start ← sender.Sender.new settings (unsigned .U64 first) 0#i64
  let final ← operations.foldlM senderStep (start, [])
  pure final.2

/-- Evaluates the function a line names on the line's arguments. -/
def evaluate (function : String) (args : List Int) : Except String (List Int) :=
  match function, args with
  | "saturate", [x] => result (fixed.saturate (signed .I128 x)) (fun r => [r.val])
  | "mul_shift", [a, b, shift] =>
    result (fixed.mul_shift (signed .I64 a) (signed .I64 b) (unsigned .U32 shift))
      (fun r => [r.val])
  | "div_floor", [a, b] =>
    result (fixed.div_floor (signed .I128 a) (signed .I64 b)) (fun r => [r.val])
  | "relation", span :: limit :: count :: rest =>
    match triples rest with
    | some packets =>
      if packets.length = count then result (runRelation span limit packets) id
      else .error "the number of packets is not the stated one"
    | none => .error "packets are not triples"
  | "presence", count :: rest =>
    match triples rest with
    | some operations =>
      if operations.length = count then result (runPresence operations) id
      else .error "the number of operations is not the stated one"
    | none => .error "operations are not triples"
  | "receiver", silence :: count :: rest =>
    match groups 8 rest with
    | some operations =>
      if operations.length = count then result (runReceiver silence operations) id
      else .error "the number of operations is not the stated one"
    | none => .error "operations are not groups of eight"
  | "sender", first :: count :: rest =>
    match groups 4 rest with
    | some operations =>
      if operations.length = count then result (runSender first operations) id
      else .error "the number of operations is not the stated one"
    | none => .error "operations are not groups of four"
  | "sender_time", [time, value, rise, run, path, moment] =>
    result (timing.sender_time
      { time := signed .I64 time, value := signed .I64 value, rise := signed .I64 rise,
        run := signed .I64 run } (signed .I64 path) (signed .I64 moment)) (fun r => [r.val])
  | "due", [index, capture, rate, drift, level, slope, moment] =>
    result (timing.due
      { index := unsigned .U64 index, capture := signed .I64 capture,
        rate := unsigned .U32 rate, drift := signed .I32 drift, level := signed .I64 level,
        level_slope := signed .I32 slope } (signed .I64 moment))
      (fun r => match r with
        | some p => [1, p.frame.val, p.fraction.val]
        | none => [0, 0, 0])
  | "distance", [frame, fraction, laterFrame, laterFraction] =>
    result (timing.distance
      { frame := unsigned .U64 frame, fraction := unsigned .U64 fraction }
      { frame := unsigned .U64 laterFrame, fraction := unsigned .U64 laterFraction })
      (fun r => [r.val])
  | "advance", [frame, fraction, frames, step] =>
    result (timing.advance
      { frame := unsigned .U64 frame, fraction := unsigned .U64 fraction }
      (unsigned .U32 frames) (signed .I64 step)) (fun r => [r.frame.val, r.fraction.val])
  | "player", gain :: limit :: jump :: count :: rest =>
    match groups 6 rest with
    | some cycles =>
      if cycles.length = count then result (runPlayer gain limit jump cycles) id
      else .error "the number of cycles is not the stated one"
    | none => .error "cycles are not groups of six"
  | "parse_audio", bytes => result (runParse bytes) id
  | "write_audio", fields => result (runWrite fields) id
  | _, _ => .error s!"no function {function} with {args.length} arguments"
where
  result {α : Type} (r : Result α) (values : α → List Int) : Except String (List Int) :=
    match r.match with
    | .ok v => .ok (values v)
    | .vis _ _ => .error "the translation fails"
    | .div => .error "the translation does not terminate"

/-- Checks one line; the error says what differs. -/
def checkLine (line : String) : Except String Unit := do
  let words := line.splitOn " "
  let (call, expected) ← match words.splitOn "->" with
    | [call, expected] => pure (call, expected)
    | _ => throw "not of the form: name arguments -> results"
  let number (word : String) : Except String Int :=
    match word.toInt? with
    | some n => pure n
    | none => throw s!"not a number: {word}"
  match call with
  | [] => throw "no function name"
  | function :: args =>
    let got ← evaluate function (← args.mapM number)
    let want ← expected.mapM number
    unless got = want do
      throw s!"the translation gives {got}"

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: TranslationCheck.lean FILE"
    return 2
  let lines := (← IO.FS.lines path).filter (· ≠ "")
  let mut failures := 0
  for line in lines do
    if let .error reason := checkLine line then
      failures := failures + 1
      if failures ≤ 20 then
        IO.eprintln s!"{line}: {reason}"
  IO.println s!"{lines.size} lines compared, {failures} differ"
  return if failures = 0 ∧ lines.size > 0 then 0 else 1
