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
