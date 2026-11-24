/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Memory
public import Unisono.Spec.MoreInMessages

/-!
# The controller: playback at a level that the sender announces

The baseline (`Unisono.Solutions.FixedDelay`) plays at a latency that is
configured, trusts the timestamps of its devices, and assumes that the
clocks of the hosts run at one rate. The solution of this file sends the
baseline's messages with further fields, and plays differently.

* **The level.** The sender announces, with every block of the source, the
  *level* of the block's first frame and the slope of the level: the latency
  that every speaker is to hold for that frame, and by how much the level
  changes from one frame to the next. How the sender chooses the level is a
  parameter of the solution (`LevelRule`).
* **The capture line.** The capture device has a clock of its own, and its
  timestamps need not be exact. The sender estimates, from the timestamps of
  the blocks handed over so far, the reading of its clock at which each frame
  was captured, as a line in the frame's number (`DeviceEstimator`). Every
  block carries the capture time of its first frame and the time from one
  frame to the next, both on the sender's clock and both from that line.
* **The schedule.** A frame is *due* when the sender's clock reads the
  frame's capture time plus its level.
* **The clock line.** Each receiving host estimates the sender's clock as a
  line in its own clock, from its clock exchanges with the sender
  (`ClockEstimator`). The sender's host uses its own clock.
* **The device line.** Each host estimates, from the timestamps of the
  blocks that a playback device has requested so far, the reading of its own
  clock at which each output sample leaves, as a line in the sample's number.
* **The position.** When a speaker's device requests a block, the host finds
  for each output sample the reading of its own clock at which the sample
  leaves (device line), the reading of the sender's clock at that moment
  (clock line), and the position that is due then (schedule). The speaker
  plays that position.

The estimators are parameters. The theorems about this solution hold for
every estimator that is exact on undisturbed data (`ClockEstimator.Exact`,
`DeviceEstimator.Exact`); `twoExchanges` and `twoReports` are such
estimators.

The solution sends what the baseline sends, with more in each message
(`sendsMore`), so its run is the baseline's run once the further fields are
forgotten (`Unisono.Spec.MoreInMessages`).

Not yet in this solution: a pace that changes smoothly when an estimate
changes, the measurement of what each frame needs, and a rule that chooses
the level from those measurements.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- What the controller's messages carry besides frames of the source: the
fields of the baseline's messages, and further ones. -/
inductive Payload where
  /-- A block of the source: its first frame and the capture device's
  timestamp of that frame, as in the baseline; the sender's estimate of the
  reading of its clock at which that frame was captured; its estimate of the
  time from one frame to the next, on its clock; the level of that frame, in
  seconds of the sender's clock; and by how much the level changes from one
  frame to the next. -/
  | block (first : ℕ) (stamp : ℝ) (capture : ℝ) (period : ℝ) (level : ℝ) (slope : ℝ)
  /-- A clock query: the querying host's clock reading when it sends the
  query, as in the baseline, and the most that a frame has needed at that
  host since its last query, if it has measured any. -/
  | ask (sent : ℝ) (need : Option ℝ)
  /-- The sender's answer to a clock query, as in the baseline. -/
  | answer (sent : ℝ) (received : ℝ)

/-- A payload with the further fields forgotten: the baseline's payload. -/
def Payload.plain : Payload → FixedDelay.Payload
  | .block first stamp _ _ _ _ => .block first stamp
  | .ask sent _ => .ask sent
  | .answer sent received => .answer sent received

/-- A line: its value at zero, and its slope. -/
structure Line where
  intercept : ℝ
  slope : ℝ

/-- The value of the line at `x`. -/
def Line.eval (l : Line) (x : ℝ) : ℝ := l.intercept + l.slope * x

/-! ## Estimators -/

/-- One clock exchange, as the querying host sees it: the reading of its
clock when it sent the query, the reading of the sender's clock when the
query arrived, and the reading of its own clock when the answer arrived. -/
structure Exchange where
  sent : ℝ
  received : ℝ
  arrived : ℝ

/-- A way to estimate the sender's clock as a line in a host's clock, from
the clock exchanges so far, oldest first; `none` while there is no
estimate. -/
abbrev ClockEstimator : Type := List Exchange → Option Line

/-- The estimator is exact on undisturbed exchanges. Suppose that the
sender's reading in every exchange lies on a line of slope `c` as a function
of the reading at which the query was sent, with value `a` at zero, and on a
line of the same slope as a function of the reading at which the answer
arrived, with value `b` at zero. If two of the queries were sent at
different readings, the estimate is the line of slope `c` halfway between
the two. -/
def ClockEstimator.Exact (est : ClockEstimator) : Prop :=
  ∀ (l : List Exchange) (a b c : ℝ),
    (∀ e ∈ l, e.received = a + c * e.sent ∧ e.received = b + c * e.arrived) →
    (∃ e ∈ l, ∃ e' ∈ l, e.sent ≠ e'.sent) → est l = some ⟨(a + b) / 2, c⟩

/-- The estimator that uses two exchanges: the first one, and the first
later one whose query was sent at a different reading. The slope is the
slope between the two; the line passes halfway between the first exchange's
two samples. -/
def twoExchanges : ClockEstimator := fun l =>
  match l with
  | [] => none
  | e :: rest =>
      match rest.find? fun e' => decide (e'.sent ≠ e.sent) with
      | none => none
      | some e' =>
          some ⟨((e.received - (e'.received - e.received) / (e'.sent - e.sent) * e.sent)
              + (e.received - (e'.received - e.received) / (e'.sent - e.sent) * e.arrived)) / 2,
            (e'.received - e.received) / (e'.sent - e.sent)⟩

/-- **The two-exchange estimator is exact on undisturbed exchanges.** -/
theorem twoExchanges_exact : twoExchanges.Exact := by
  intro l a b c hall hdist
  cases l with
  | nil =>
    obtain ⟨e, he, -⟩ := hdist
    simp at he
  | cons e rest =>
    have hex : ∃ e' ∈ rest, e'.sent ≠ e.sent := by
      obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := hdist
      by_cases h : e₁.sent = e.sent
      · have hne2 : e₂.sent ≠ e.sent := fun h' => hne (h.trans h'.symm)
        rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · exact absurd (by rw [h₂']) hne2
        · exact ⟨e₂, h₂', hne2⟩
      · rcases List.mem_cons.mp h₁ with h₁' | h₁'
        · exact absurd (by rw [h₁']) h
        · exact ⟨e₁, h₁', h⟩
    obtain ⟨e₀, he₀, hne₀⟩ := hex
    cases hfind : rest.find? (fun e' => decide (e'.sent ≠ e.sent)) with
    | none =>
      have h := List.find?_eq_none.mp hfind e₀ he₀
      simp [hne₀] at h
    | some e' =>
      have hmem : e' ∈ rest := List.mem_of_find?_eq_some hfind
      have hne : e'.sent ≠ e.sent := by
        have h := List.find?_some hfind
        simpa using h
      have h1 := hall e (List.mem_cons.mpr (Or.inl rfl))
      have h2 := hall e' (List.mem_cons.mpr (Or.inr hmem))
      have hd : e'.sent - e.sent ≠ 0 := sub_ne_zero.mpr hne
      have hslope : (e'.received - e.received) / (e'.sent - e.sent) = c := by
        rw [h1.1, h2.1]
        field_simp
        ring
      have ea : e.received - c * e.sent = a := by
        rw [h1.1]
        ring
      have eb : e.received - c * e.arrived = b := by
        rw [h1.2]
        ring
      simp only [twoExchanges, hfind]
      rw [hslope, ea, eb]

/-- A way to estimate, from the timestamps that a device has reported so
far, the reading of the host's clock at which each frame or output sample of
the device occurs, as a line in its number. A report is the number of a
block's first frame or output sample and the timestamp of the block. -/
abbrev DeviceEstimator : Type := List (ℕ × ℝ) → Option Line

/-- The estimator is exact on undisturbed reports: if every timestamp is
`a + c * n` for its number `n`, and two reports have different numbers, the
estimate is that line. -/
def DeviceEstimator.Exact (est : DeviceEstimator) : Prop :=
  ∀ (l : List (ℕ × ℝ)) (a c : ℝ),
    (∀ e ∈ l, e.2 = a + c * e.1) → (∃ e ∈ l, ∃ e' ∈ l, e.1 ≠ e'.1) → est l = some ⟨a, c⟩

/-- The estimator that uses two reports: the first one, and the first later
one with a different number. -/
def twoReports : DeviceEstimator := fun l =>
  match l with
  | [] => none
  | e :: rest =>
      match rest.find? fun e' => decide (e'.1 ≠ e.1) with
      | none => none
      | some e' =>
          some ⟨e.2 - (e'.2 - e.2) / ((e'.1 : ℝ) - e.1) * e.1, (e'.2 - e.2) / ((e'.1 : ℝ) - e.1)⟩

/-- **The two-report estimator is exact on undisturbed reports.** -/
theorem twoReports_exact : twoReports.Exact := by
  intro l a c hall hdist
  cases l with
  | nil =>
    obtain ⟨e, he, -⟩ := hdist
    simp at he
  | cons e rest =>
    have hex : ∃ e' ∈ rest, e'.1 ≠ e.1 := by
      obtain ⟨e₁, h₁, e₂, h₂, hne⟩ := hdist
      by_cases h : e₁.1 = e.1
      · have hne2 : e₂.1 ≠ e.1 := fun h' => hne (h.trans h'.symm)
        rcases List.mem_cons.mp h₂ with h₂' | h₂'
        · exact absurd (by rw [h₂']) hne2
        · exact ⟨e₂, h₂', hne2⟩
      · rcases List.mem_cons.mp h₁ with h₁' | h₁'
        · exact absurd (by rw [h₁']) h
        · exact ⟨e₁, h₁', h⟩
    obtain ⟨e₀, he₀, hne₀⟩ := hex
    cases hfind : rest.find? (fun e' => decide (e'.1 ≠ e.1)) with
    | none =>
      have h := List.find?_eq_none.mp hfind e₀ he₀
      simp [hne₀] at h
    | some e' =>
      have hmem : e' ∈ rest := List.mem_of_find?_eq_some hfind
      have hne : e'.1 ≠ e.1 := by
        have h := List.find?_some hfind
        simpa using h
      have h1 := hall e (List.mem_cons.mpr (Or.inl rfl))
      have h2 := hall e' (List.mem_cons.mpr (Or.inr hmem))
      have hd : ((e'.1 : ℝ) - e.1) ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne hne)
      have hslope : (e'.2 - e.2) / ((e'.1 : ℝ) - e.1) = c := by
        rw [h1, h2]
        field_simp
        ring
      have ea : e.2 - c * e.1 = a := by
        rw [h1]
        ring
      simp only [twoReports, hfind]
      rw [hslope, ea]

/-! ## What a host reads from its view -/

/-- The clock exchanges in a view: the answers that arrived, each with the
reading at which it arrived. -/
def exchangesOf (l : List (Event H R Payload)) : List Exchange :=
  l.filterMap fun e =>
    match e.observation with
    | .received _ (.answer sent received) _ => some ⟨sent, received, e.reading⟩
    | _ => none

/-- The reports of the capture device in a view: for each block handed over,
its first frame and its timestamp. -/
def captureReports (l : List (Event H R Payload)) : List (ℕ × ℝ) :=
  l.filterMap fun e =>
    match e.observation with
    | .handed frames stamp => frames.head?.map fun f => (f.1, stamp)
    | _ => none

/-- The reports of speaker `r`'s playback device in a view: for each block
requested, its first output sample and its timestamp. -/
def playbackReports (r : Fin R) (l : List (Event H R Payload)) : List (ℕ × ℝ) :=
  l.filterMap fun e =>
    match e.observation with
    | .asked r' outputs stamp => if r' = r then outputs.head?.map fun k => (k, stamp) else none
    | _ => none

/-- What a block says about the schedule: its first frame, the capture time
of that frame and the time from one frame to the next, on the sender's
clock, the level of that frame and the change of the level from one frame to
the next. -/
structure Header where
  first : ℕ
  capture : ℝ
  period : ℝ
  level : ℝ
  slope : ℝ

/-- The position that is due when the sender's clock reads `s`, by the
header: the position `x` whose capture time plus level is `s`, where the
capture time of `x` is `capture + (x - first) * period` and its level is
`level + (x - first) * slope`. -/
def Header.due (hd : Header) (s : ℝ) : ℝ :=
  hd.first + (s - hd.capture - hd.level) / (hd.period + hd.slope)

/-- The header of the newest block that has arrived in a view: the one with
the highest first frame. -/
def headerOf (l : List (Event H R Payload)) : Option Header :=
  l.foldl
    (fun acc e =>
      match e.observation with
      | .received _ (.block f _ capture period level slope) _ =>
          match acc with
          | some hd => if hd.first < f then some ⟨f, capture, period, level, slope⟩ else acc
          | none => some ⟨f, capture, period, level, slope⟩
      | _ => acc)
    none

/-- A rule by which the sender chooses the level: from its view when the
capture device hands over a block, and the block's first frame, the level of
that frame and the change of the level from one frame to the next. -/
abbrev LevelRule (H : Type) (R : ℕ) : Type := List (Event H R Payload) → ℕ → ℝ × ℝ

/-- The rule that holds the level at `L`. -/
def constantLevel (L : ℝ) : LevelRule H R := fun _ _ => (L, 0)

variable [DecidableEq H] (p : FixedDelay.Params H) (clockEst : ClockEstimator)
  (deviceEst : DeviceEstimator) (levelRule : LevelRule H R)

/-- The header of a block that the capture device hands over, given the
sender's view up to and including the handover: the capture time of the
block's first frame `f` and the time from one frame to the next come from
the line through the capture device's reports, or from the block's own
timestamp and the nominal rate while there is no line; the level and its
slope come from the level rule. -/
def blockHeader (view : List (Event H R Payload)) (f : ℕ) (stamp : ℝ) : Header :=
  ⟨f, ((deviceEst (captureReports view)).map fun ln => ln.eval f).getD stamp,
    ((deviceEst (captureReports view)).map Line.slope).getD (1 / p.rate),
    (levelRule view f).1, (levelRule view f).2⟩

/-- The header of the newest block that the sender's own capture device has
handed over in a view: the header that the sender put in that block. -/
def ownHeaderOf (l : List (Event H R Payload)) : Option Header :=
  (l.foldl
    (fun (acc : List (Event H R Payload) × Option Header) e =>
      (acc.1 ++ [e],
        match e.observation with
        | .handed frames stamp =>
            match frames.head? with
            | some f => some (blockHeader p deviceEst levelRule (acc.1 ++ [e]) f.1 stamp)
            | none => acc.2
        | _ => acc.2))
    ([], none)).2

/-- A message of the baseline with the controller's further fields, as host
`h` fills them in at the view `view`. -/
def enrich (view : List (Event H R Payload)) : FixedDelay.Payload → Payload
  | .block f stamp =>
      .block f stamp (blockHeader p deviceEst levelRule view f stamp).capture
        (blockHeader p deviceEst levelRule view f stamp).period
        (blockHeader p deviceEst levelRule view f stamp).level
        (blockHeader p deviceEst levelRule view f stamp).slope
  | .ask sent => .ask sent none
  | .answer sent received => .answer sent received

omit [DecidableEq H] in
/-- Forgetting the further fields of an enriched message gives the message
back. -/
theorem plain_enrich (view : List (Event H R Payload)) (x : FixedDelay.Payload) :
    (enrich p deviceEst levelRule view x).plain = x := by
  cases x <;> rfl

/-- A host's estimate of the sender's clock after the events `l`: its own
clock at the sender's host, and the estimator's line elsewhere. -/
def clockOf (h : H) (l : List (Event H R Payload)) : Option Line :=
  if h = p.sender then some ⟨0, 1⟩ else clockEst (exchangesOf l)

/-- The schedule that a host follows after the events `l`: the header of the
newest block that has arrived, or at the sender's host the header of the
newest block handed over. -/
def scheduleOf (h : H) (l : List (Event H R Payload)) : Option Header :=
  if h = p.sender then ownHeaderOf p deviceEst levelRule l else headerOf l

/-- The position that output sample `k` plays: the position that is due, by
the schedule `hd`, when the sample leaves. The device line `dl` gives the
reading of the host's clock at which the sample leaves; while there is no
device line, the reading is taken from the timestamp `stamp` of the block,
whose first output sample is `first`, at the nominal rate. The clock line
`cl` gives the reading of the sender's clock at that moment. There is no
position while the host has no schedule or no clock line. -/
def position (hd : Option Header) (cl dl : Option Line) (first : ℕ) (stamp : ℝ) (k : ℕ) :
    Option ℝ :=
  match hd, cl with
  | some hd, some cl =>
      some (hd.due (cl.eval ((dl.map fun dl => dl.eval k).getD
        (stamp + ((k : ℝ) - first) / p.rate))))
  | _, _ => none

/-- The controller: each host sends what the baseline sends, with the
further fields, and plays each output sample at the position that is due
when the sample leaves. -/
def solution : Solution H R Payload := fun h view =>
  { sends := ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
        (view.map (Event.mapMsg Payload.plain))).sends.map
      fun s => (s.1, enrich p deviceEst levelRule view s.2.1, s.2.2)
    timers := ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
        (view.map (Event.mapMsg Payload.plain))).timers
    plays :=
      match view.getLast? with
      | some e =>
          match e.observation with
          | .asked r outputs stamp =>
              position p (scheduleOf p deviceEst levelRule h view) (clockOf p clockEst h view)
                (deviceEst (playbackReports r view)) (outputs.headD 0) stamp
          | _ => fun _ => none
      | none => fun _ => none }

/-- **The controller sends what the baseline sends, with more in each
message.** -/
theorem sendsMore :
    (solution p clockEst deviceEst levelRule : Solution H R Payload).SendsMore
      (FixedDelay.solution p) Payload.plain := by
  intro h v
  refine ⟨?_, rfl⟩
  show mapSends Payload.plain
      (((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
          (v.map (Event.mapMsg Payload.plain))).sends.map
        fun s => (s.1, enrich p deviceEst levelRule v s.2.1, s.2.2)) = _
  rw [mapSends, List.map_map]
  conv_rhs => rw [← List.map_id ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
    (v.map (Event.mapMsg Payload.plain))).sends]
  refine List.map_congr_left fun s _ => ?_
  simp [plain_enrich]

/-- What the controller plays at a device request. -/
theorem plays_asked (h : H) (l : List (Event H R Payload)) (reading : ℝ) (r : Fin R)
    (outputs : List ℕ) (stamp : ℝ) :
    ((solution p clockEst deviceEst levelRule : Solution H R Payload) h
        (l ++ [⟨reading, .asked r outputs stamp⟩])).plays
      = position p
          (scheduleOf p deviceEst levelRule h (l ++ [⟨reading, .asked r outputs stamp⟩]))
          (clockOf p clockEst h (l ++ [⟨reading, .asked r outputs stamp⟩]))
          (deviceEst (playbackReports r (l ++ [⟨reading, .asked r outputs stamp⟩])))
          (outputs.headD 0) stamp := by
  simp [solution]

end Unisono.Solutions.Controller
