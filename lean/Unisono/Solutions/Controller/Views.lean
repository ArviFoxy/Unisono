/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller
public import Unisono.Solutions.FixedDelay.Arrivals

/-!
# What the controller's hosts read from their views

Facts about the run of the controller in any world.

* The timestamps that a host has collected from a playback device are those
  of the requests that the device has made, each with the first output
  sample of its block (`mem_playbackReports`); the same holds for the capture
  device and the blocks it has handed over (`mem_captureReports`).
* The clock exchanges in a view are those of the view with the further
  fields forgotten (`exchangesOf_eq`).
* The schedule of a receiving host holds exactly the headers of the blocks
  that arrived, each with the number of frames that its message carried
  (`mem_headersOf`, `headersOf_mem`).
* Every block in transit carries the header that the sender computed when
  the capture device handed the block over, from its view at that moment
  (`block_header`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- A capture block begins with its first frame. -/
theorem CaptureDevice.head?_block (d : CaptureDevice) (b : ℕ) :
    (d.block b).head? = some (d.first b) := by
  unfold CaptureDevice.block
  have hlt := d.first_strictMono (Nat.lt_succ_self b)
  obtain ⟨len, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hlt)
  rw [hlen]
  rfl

/-- A playback block begins with its first output sample. -/
theorem PlaybackDevice.head?_block (d : PlaybackDevice) (b : ℕ) :
    (d.block b).head? = some (d.first b) := by
  unfold PlaybackDevice.block
  have hlt := d.first_strictMono (Nat.lt_succ_self b)
  obtain ⟨len, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hlt)
  rw [hlen]
  rfl

end Unisono.Spec

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- The baseline sends a block only at the sender, when the capture device
hands over a block with that first frame and that timestamp. -/
theorem act_sends_block (h : H) (mem : Memory H R) (e : Event H R Payload)
    {s : H × Payload × Finset ℕ} (hs : s ∈ (act p h mem e).sends) {fr : ℕ} {stamp : ℝ}
    (hb : s.2.1 = .block fr stamp) :
    h = p.sender ∧ ∃ frames t₀, e.observation = .handed frames stamp
      ∧ frames.head? = some (fr, t₀) := by
  unfold act at hs
  cases hobs : e.observation with
  | handed frames stamp' =>
    simp only [hobs] at hs
    split_ifs at hs with hsend
    · cases hhead : frames.head? with
      | none => simp [hhead] at hs
      | some fs =>
        obtain ⟨f₀, t₀⟩ := fs
        simp only [hhead, List.mem_flatMap, List.mem_filter, List.mem_replicate,
          decide_eq_true_eq] at hs
        obtain ⟨j, -, -, rfl⟩ := hs
        simp only [Payload.block.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨hsend, frames, t₀, rfl, hhead⟩
    · simp at hs
  | received i payload F =>
    cases payload with
    | block _ _ => simp [hobs] at hs
    | ask sent =>
      simp only [hobs] at hs
      split_ifs at hs with hc
      · rw [List.mem_replicate] at hs
        obtain ⟨-, rfl⟩ := hs
        simp at hb
      · simp at hs
    | answer _ _ => simp [hobs] at hs
  | asked r outputs stamp' =>
    simp only [hobs] at hs
    split_ifs at hs with ha
    · rw [List.mem_replicate] at hs
      obtain ⟨-, rfl⟩ := hs
      simp at hb
    · simp at hs
  | timer => simp [hobs] at hs

end Unisono.Solutions.FixedDelay

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-! ## Clock exchanges -/

/-- The clock exchanges in a view of the baseline: the answers that arrived,
each with the reading at which it arrived. -/
def plainExchangesOf (l : List (Event H R FixedDelay.Payload)) : List Exchange :=
  l.filterMap fun e =>
    match e.observation with
    | .received _ (.answer sent received) _ => some ⟨sent, received, e.reading⟩
    | _ => none

/-- The clock exchanges in a view of the controller are those of the view
with the further fields forgotten. -/
theorem exchangesOf_eq (l : List (Event H R Payload)) :
    exchangesOf l = plainExchangesOf (l.map (Event.mapMsg Payload.plain)) := by
  unfold exchangesOf plainExchangesOf
  rw [List.filterMap_map]
  refine List.filterMap_congr fun e _ => ?_
  obtain ⟨reading, obs⟩ := e
  cases obs with
  | handed frames stamp => rfl
  | asked r outputs stamp => rfl
  | timer => rfl
  | received i c F => cases c <;> rfl

/-- An exchange of a view of the baseline comes from an answer in the
view. -/
theorem mem_plainExchangesOf {l : List (Event H R FixedDelay.Payload)} {x : Exchange}
    (hx : x ∈ plainExchangesOf l) :
    ∃ e ∈ l, ∃ i F, e.observation = .received i (.answer x.sent x.received) F
      ∧ e.reading = x.arrived := by
  obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp hx
  refine ⟨e, he, ?_⟩
  cases hobs : e.observation with
  | handed frames stamp => simp [hobs] at hfe
  | asked r outputs stamp => simp [hobs] at hfe
  | timer => simp [hobs] at hfe
  | received i payload F =>
    cases payload with
    | block f stamp => simp [hobs] at hfe
    | ask sent => simp [hobs] at hfe
    | answer sent received =>
      simp only [hobs, Option.some.injEq] at hfe
      subst hfe
      exact ⟨i, F, rfl, rfl⟩

/-- An answer in a view of the baseline is an exchange of the view. -/
theorem plainExchangesOf_mem {l : List (Event H R FixedDelay.Payload)}
    {e : Event H R FixedDelay.Payload} (he : e ∈ l) {i : H} {sent received : ℝ}
    {F : Finset ℕ} (hobs : e.observation = .received i (.answer sent received) F) :
    (⟨sent, received, e.reading⟩ : Exchange) ∈ plainExchangesOf l :=
  List.mem_filterMap.mpr ⟨e, he, by simp [hobs]⟩

/-! ## The schedule of a receiving host -/

/-- Every header in the schedule of a receiving host is the header of a block
that arrived, with the number of frames that its message carried. -/
theorem mem_headersOf {l : List (Event H R Payload)} {x : Header × ℕ}
    (hx : x ∈ headersOf l) :
    ∃ e ∈ l, ∃ i stamp F, e.observation
        = .received i (.block x.1.first stamp x.1.capture x.1.period x.1.level x.1.slope) F
      ∧ x.2 = F.card := by
  obtain ⟨e, he, hsome⟩ := List.mem_filterMap.mp hx
  refine ⟨e, he, ?_⟩
  cases hobs : e.observation with
  | handed frames stamp => simp [hobs] at hsome
  | asked r outputs stamp => simp [hobs] at hsome
  | timer => simp [hobs] at hsome
  | received i c F =>
    cases c with
    | ask sent need => simp [hobs] at hsome
    | answer sent received => simp [hobs] at hsome
    | block f stamp capture period level slope =>
      simp only [hobs, Option.some.injEq] at hsome
      subst hsome
      exact ⟨i, stamp, F, rfl, rfl⟩

/-- The header of every block that arrived is in the schedule of the host,
with the number of frames that its message carried. -/
theorem headersOf_mem {l : List (Event H R Payload)} {e : Event H R Payload} (he : e ∈ l)
    {i : H} {f : ℕ} {stamp capture period level slope : ℝ} {F : Finset ℕ}
    (ho : e.observation = .received i (.block f stamp capture period level slope) F) :
    ((⟨f, capture, period, level, slope⟩ : Header), F.card) ∈ headersOf l :=
  List.mem_filterMap.mpr ⟨e, he, by simp [ho]⟩

/-- A device request adds nothing to the schedule of a host. -/
theorem headersOf_append_asked (l : List (Event H R Payload)) (reading : ℝ) (r : Fin R)
    (outputs : List ℕ) (stamp : ℝ) :
    headersOf (l ++ [⟨reading, .asked r outputs stamp⟩]) = headersOf l := by
  simp [headersOf, List.filterMap_append]

/-! ## The timestamps of the devices -/

variable [DecidableEq H] (w : World H R)

/-- The timestamps that a host has collected from a playback device are
those of requests of the device, each with the first output sample of its
block. -/
theorem mem_playbackReports (σ : Solution H R Payload) (lookahead : ℕ+) {n : ℕ} {h : H}
    {r : Fin R} {x : ℕ × ℝ}
    (hx : x ∈ playbackReports r ((σ.states w lookahead n).views h)) :
    ∃ b, x = ((w.speaker r).first b, (w.speaker r).reported b) := by
  obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp hx
  obtain ⟨i, -, t, obs, hhi, rfl⟩ := Solution.handled_of_mem_views w σ lookahead he
  cases obs with
  | handed frames stamp => simp at hfe
  | received j c F => simp at hfe
  | timer => simp at hfe
  | asked r' outputs stamp =>
    dsimp only at hfe
    split_ifs at hfe with hr
    · subst hr
      have hearly := Solution.handled_asked w σ lookahead hhi
      have hh := Solution.handled_of_asked w σ lookahead hearly
      rw [hhi] at hh
      simp only [Option.some.injEq, Prod.mk.injEq, Observation.asked.injEq, true_and] at hh
      obtain ⟨-, -, houts, hst⟩ := hh
      rw [houts, PlaybackDevice.head?_block, Option.map_some, Option.some.injEq] at hfe
      exact ⟨_, by rw [← hfe, hst]⟩

/-- The timestamps that the sender has collected from the capture device are
those of blocks handed over, each with the block's first frame. -/
theorem mem_captureReports (σ : Solution H R Payload) (lookahead : ℕ+) {n : ℕ} {h : H}
    {x : ℕ × ℝ} (hx : x ∈ captureReports ((σ.states w lookahead n).views h)) :
    ∃ b, x = (w.source.first b, w.source.reported b) := by
  obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp hx
  obtain ⟨i, -, t, obs, hhi, rfl⟩ := Solution.handled_of_mem_views w σ lookahead he
  cases obs with
  | asked r outputs stamp => simp at hfe
  | received j c F => simp at hfe
  | timer => simp at hfe
  | handed frames stamp =>
    dsimp only at hfe
    obtain ⟨b, -, -, hframes, hstamp⟩ := Solution.handled_handed w σ lookahead hhi
    rw [hframes, List.head?_map, CaptureDevice.head?_block, Option.map_some, Option.map_some,
      Option.some.injEq] at hfe
    exact ⟨b, by rw [← hfe, hstamp]⟩

/-! ## The headers of the blocks in transit -/

variable (p : FixedDelay.Params H) (clockEst : ClockEstimator) (deviceEst : DeviceEstimator)
  (levelRule : LevelRule H R)

/-- The controller sends a block only at the sender, when the capture device
hands over a block with that first frame and that timestamp, and the block
carries the header that the sender computes from its view then. -/
theorem sends_block (h : H) (l : List (Event H R Payload)) (e : Event H R Payload)
    {s : H × Payload × Finset ℕ}
    (hs : s ∈ ((solution p clockEst deviceEst levelRule : Solution H R Payload) h
      (l ++ [e])).sends)
    {fr : ℕ} {stamp c pd lv sl : ℝ} (hb : s.2.1 = .block fr stamp c pd lv sl) :
    h = p.sender ∧ (∃ frames t₀, e.observation = .handed frames stamp
        ∧ frames.head? = some (fr, t₀))
      ∧ (⟨fr, c, pd, lv, sl⟩ : Header)
        = blockHeader p deviceEst levelRule (l ++ [e]) fr stamp := by
  change s ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
      ((l ++ [e]).map (Event.mapMsg Payload.plain))).sends.map
    (fun s => (s.1, enrich p deviceEst levelRule h (l ++ [e]) s.2.1, s.2.2)) at hs
  obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
  dsimp only at hb
  rw [List.map_append, List.map_cons, List.map_nil, FixedDelay.solution_append] at hs₀
  cases hpl : s₀.2.1 with
  | ask sent =>
    rw [hpl] at hb
    simp [enrich] at hb
  | answer sent received =>
    rw [hpl] at hb
    simp [enrich] at hb
  | block f' st' =>
    rw [hpl] at hb
    simp only [enrich, Payload.block.injEq] at hb
    obtain ⟨rfl, rfl, hc, hpd, hlv, hsl⟩ := hb
    obtain ⟨hh, frames, t₀, hobs, hhead⟩ := FixedDelay.act_sends_block p h _ _ hs₀ hpl
    refine ⟨hh, ⟨frames, t₀, ?_, hhead⟩, ?_⟩
    · obtain ⟨reading, obs⟩ := e
      cases obs with
      | handed frames' stamp' =>
        simpa [Event.mapMsg, Observation.mapMsg] using hobs
      | asked r outputs stamp' => simp [Event.mapMsg, Observation.mapMsg] at hobs
      | received i c' F => simp [Event.mapMsg, Observation.mapMsg] at hobs
      | timer => simp [Event.mapMsg, Observation.mapMsg] at hobs
    · rw [← hc, ← hpd, ← hlv, ← hsl]
      rfl

/-- **Every block in transit carries the header that the sender computed at
its handover.** A block of the controller in transit was sent when the
capture device handed over some block `b`; it carries that block's first
frame and timestamp, and the header that the sender computed from its view
at that moment. -/
theorem block_header (lookahead : ℕ+) (n : ℕ)
    {msg : InFlight H Payload}
    (hm : msg ∈ ((solution p clockEst deviceEst levelRule : Solution H R Payload).states w
      lookahead n).inFlight)
    {fr : ℕ} {stamp c pd lv sl : ℝ} (hc : msg.contents = .block fr stamp c pd lv sl) :
    ∃ i < n, ∃ b,
      (solution p clockEst deviceEst levelRule : Solution H R Payload).handled w lookahead i
          = some (w.sender, w.source.handed b,
            .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
        ∧ fr = w.source.first b ∧ stamp = w.source.reported b
        ∧ (⟨fr, c, pd, lv, sl⟩ : Header)
          = blockHeader p deviceEst levelRule
            (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w
                lookahead i).views w.sender
              ++ [⟨(w.clock w.sender).read (w.source.handed b),
                .handed ((w.source.block b).map fun k => (k, w.target k))
                  (w.source.reported b)⟩])
            (w.source.first b) (w.source.reported b) := by
  induction n with
  | zero => simp [Solution.states, State.start] at hm
  | succ n ih =>
    rcases Solution.mem_inFlight_succ w _ lookahead n hm with hold | ⟨h, t, obs, hh, s, hs, -, -, hcont, -, -⟩
    · obtain ⟨i, hi, rest⟩ := ih hold
      exact ⟨i, Nat.lt_succ_of_lt hi, rest⟩
    · rw [hcont] at hc
      obtain ⟨hhs, ⟨frames, t₀, hobs, hhead⟩, hheader⟩ :=
        sends_block p clockEst deviceEst levelRule h _ _ hs hc
      dsimp only at hobs
      subst hobs
      obtain ⟨b, hhw, ht, hframes, hstamp⟩ := Solution.handled_handed w _ lookahead hh
      subst hhw ht hframes hstamp
      have hfr : fr = w.source.first b := by
        rw [List.head?_map, CaptureDevice.head?_block, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hhead
        exact hhead.1.symm
      subst hfr
      exact ⟨n, Nat.lt_succ_self n, b, hh, rfl, rfl, hheader⟩

end Unisono.Solutions.Controller
