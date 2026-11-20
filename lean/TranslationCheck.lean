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
    h.stamped_index.val, h.stamped_departure.val]

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
  | .Err reason => pure (rejection reason ++ List.replicate 15 0)

/-- Writes a header given by its fields into 256 zero bytes, and returns the
length that writing reports and the first 80 bytes. -/
def runWrite (f : List Int) : Result (List Int) := do
  match f with
  | [stream, timeline, index, capture, rate, frames, channels, format, level, slope, span,
      window, flags, protection, stampedIndex, stampedDeparture] =>
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
      stamped_departure := signed .I64 stampedDeparture }
    let (length, bytes) ← packet.write_audio header (byteSlice (List.replicate 256 0))
    match length with
    | some n => pure (n.val :: (bytes.val.take 80).map (·.val))
    | none => pure [-1]
  | _ => pure [-2]

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
