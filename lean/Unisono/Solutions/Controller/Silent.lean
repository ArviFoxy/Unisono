/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Arrived
public import Unisono.Spec.FollowerRun

/-!
# When an output sample of the controller plays nothing

The controller with the schedule of the knots, the level rule `knotLevel`
and playback that follows the position that is due, in a world without loss
(`KnotSetting`). An output sample of a speaker on a host other than the
sender's plays nothing only for one of these reasons (`followed_silent`):

* the host has no estimate of the sender's clock, or its estimate lies
  before the edge of the first block: these are the output samples before
  the stream reaches the host;
* a block whose edge is at or before the estimate arrived at or after the
  request: the block that holds the position that is due had not arrived;
* the position that is due lies within `J - u` frames of the start of the
  stream;
* a block whose first frame lies less than `J - u` plus the lookahead after
  the position that is due arrived at or after the request.

In the last three cases the stream, or a block that the output sample
needs, came late. Nothing is assumed about clocks or delays beyond the
setting.

Also here:

* `ruled_mem_held_iff`: at a request, the host holds a frame exactly when
  the message of the frame's block arrived before the request.
* `Follows.none_iff`: the follower gives nothing exactly where the target is
  unknown.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- Every frame belongs to a block of the capture device. -/
theorem CaptureDevice.exists_block (d : CaptureDevice) (n : ℕ) : ∃ b, n ∈ d.block b := by
  classical
  have hm := d.first_strictMono
  have hex : ∃ b, n < d.first (b + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (hm.id_le (n + 1))⟩
  refine ⟨Nat.find hex, ?_⟩
  have hspec := Nat.find_spec hex
  have hlow : d.first (Nat.find hex) ≤ n := by
    cases hb : Nat.find hex with
    | zero =>
      rw [d.first_zero]
      exact Nat.zero_le n
    | succ b =>
      have hmin := Nat.find_min hex (show b < Nat.find hex by omega)
      exact not_lt.mp hmin
  unfold CaptureDevice.block
  rw [List.mem_range'_1]
  have h2 : d.first (Nat.find hex) ≤ d.first (Nat.find hex + 1) := (hm (Nat.lt_succ_self _)).le
  omega

/-- The first frame of the block of a frame is at most the frame. -/
theorem CaptureDevice.first_le_of_mem (d : CaptureDevice) {n b : ℕ} (h : n ∈ d.block b) :
    d.first b ≤ n := by
  unfold CaptureDevice.block at h
  rw [List.mem_range'_1] at h
  exact h.1

/-- **The follower gives nothing exactly where the target is unknown.** -/
theorem Follows.none_iff {u J : ℝ} {ξ : ℕ → ℝ} {X c : ℕ → Option ℝ} (h : Follows u J ξ X c)
    (k : ℕ) : c k = none ↔ X k = none := by
  constructor
  · intro hc
    cases k with
    | zero =>
      rw [← h.start]
      exact hc
    | succ k =>
      rw [h.step k] at hc
      exact followStep_eq_none hc
  · intro hX
    cases k with
    | zero => rw [h.start, hX]
    | succ k => rw [h.step k, hX, followStep_none_right]

end Unisono.Spec

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- The setting of the theorems on the controller with the schedule of the
knots: a world without loss whose devices hand over and request blocks
without end, rules with the capture schedule of the knots and the level
rule `knotLevel`, a share from zero to less than one, and a positive time
from one frame to the next for the first block. -/
structure KnotSetting (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    (A : H → H → Time → Time) (q : LevelSettings) (share nominal : ℝ) : Prop where
  noLoss : NoLoss p w A
  capture : rules.capture = knotCapture nominal
  level : ∃ need, rules.level = knotLevel q share nominal need
  share_nonneg : 0 ≤ share
  share_lt_one : share < 1
  nominal_pos : 0 < nominal
  handed : ∀ T, ∃ b, T < w.source.handed b
  asked : ∀ r T, ∃ b, T < (w.speaker r).asked b

variable {p : FixedDelay.Params H} {rules : Rules H R} {w : World H R}
  {A : H → H → Time → Time} {q : LevelSettings} {share nominal : ℝ}

/-- In the setting, the run handles every handover. -/
theorem KnotSetting.handovers (hK : KnotSetting p rules w A q share nominal) (lookahead : ℕ+)
    (b : ℕ) :
    ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)) :=
  ruled_handover_step p rules w hK.handed hK.asked lookahead b

/-- In the setting, the run handles every request. -/
theorem KnotSetting.requests (hK : KnotSetting p rules w A q share nominal) (lookahead : ℕ+)
    (r : Fin R) (b : ℕ) :
    ∃ n, earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
      ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r b) :=
  ruled_request_step p rules w hK.handed hK.asked lookahead r b

/-- **A host holds a frame exactly when its block arrived.** In a world
without loss, at the step that handles the request of block `β` of a
speaker on a host other than the sender's, the host holds a frame of the
source exactly when the message of the frame's block arrived before the
request. -/
theorem ruled_mem_held_iff (hN : NoLoss p w A) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    {m b : ℕ} (hm : m ∈ w.source.block b) :
    m ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).held (w.host r)
      ↔ A w.sender (w.host r) (w.source.handed b) < (w.speaker r).asked β := by
  have hmore := ruled_sendsMore (R := R) p rules
  have hnext := Solution.askedNext_of_earliest _ w lookahead hE
  rw [Solution.held_forget w Payload.plain lookahead hmore n]
  refine FixedDelay.mem_held_iff_arrived p w lookahead hN.deliver hN.sender hN.nodup hN.copies
    (hN.speakers r) hr ?_ ?_ hm
  · rw [← Solution.askedNext_forget w Payload.plain lookahead hmore n]
    exact hnext
  · rw [← (Solution.earliest_forget w Payload.plain lookahead hmore n).2]
    exact hE

/-- **When an output sample plays nothing.** In the setting `KnotSetting`,
take the controller with playback that follows the position that is due,
for `0 ≤ u ≤ J`. Let speaker `r` be on a host other than the sender's, let
step `n` handle the request of block `β`, and let output sample `k` of that
block play nothing. Then the host has no estimate; or it has an estimate
`s` and one of these holds:

* `s` lies before the edge of block zero;
* some block whose edge is at or before `s` arrived at or after the request;
* `s` lies between the edges of a block `b` and the next, and with `x` the
  position that the header of `b` gives for `s`, moved back by
  `rules.back`: `x < J - u`, or some block whose first frame is less than
  `x + J - u` plus the lookahead arrived at or after the request. -/
theorem followed_silent (hK : KnotSetting p rules w A q share nominal) (lookahead : ℕ+)
    {u J : ℝ} (huJ : u ≤ J) {n : ℕ} {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hk : k ∈ (w.speaker r).block β)
    (hsilent : ((ruled p rules : Solution H R Payload).followed u J).plays w lookahead r k
      = none) :
    rules.reading (w.host r)
        (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
          ++ [w.askedEvent r β]) r k = none
      ∨ ∃ s, rules.reading (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β]) r k = some s
        ∧ (s < dueEdge p rules w lookahead q share nominal 0
          ∨ (∃ b, dueEdge p rules w lookahead q share nominal b ≤ s
              ∧ (w.speaker r).asked β ≤ A w.sender (w.host r) (w.source.handed b))
          ∨ ∃ b x, dueEdge p rules w lookahead q share nominal b ≤ s
              ∧ s < dueEdge p rules w lookahead q share nominal (b + 1)
              ∧ x = w.source.first b + (s - dueEdge p rules w lookahead q share nominal b)
                  / dueSlope p rules w lookahead q share nominal b - rules.back
              ∧ (x < J - u
                ∨ ∃ b', (w.source.first b' : ℝ) < x + (J - u) + (lookahead : ℕ)
                    ∧ (w.speaker r).asked β
                      ≤ A w.sender (w.host r) (w.source.handed b'))) := by
  classical
  obtain ⟨need, hlev⟩ := hK.level
  have hprog := hK.handovers lookahead
  have hreq := hK.requests lookahead r
  have hiff := fun x => ruled_chosen_iff (x := x) hK.capture hlev hK.share_nonneg
    hK.share_lt_one hK.nominal_pos hK.noLoss lookahead hprog hr hE k
  have hfol := (ruled p rules : Solution H R Payload).followed_follows w lookahead u J hreq
  have hX : (ruled p rules : Solution H R Payload).chosen w lookahead r k
      = (ruled p rules : Solution H R Payload).chosenAt w lookahead n r β k :=
    Solution.chosen_eq _ w lookahead hk hE
  -- The step in the run with the follower.
  have hnext := Solution.askedNext_of_earliest _ w lookahead hE
  have hE' := ((Solution.stepped_asked_iff (ruled p rules : Solution H R Payload)
    (followStep u J) w lookahead n r β).mpr ⟨hnext, hE⟩).2
  have hplays := Solution.plays_eq_playable_chosen
    ((ruled p rules : Solution H R Payload).followed u J) w lookahead hk hE'
  rw [hplays] at hsilent
  have hheld : (((ruled p rules : Solution H R Payload).followed u J).states w lookahead n).held
      = ((ruled p rules : Solution H R Payload).states w lookahead n).held :=
    Solution.held_eq_of_sends_eq w lookahead
      (σ := (ruled p rules : Solution H R Payload).followed u J) (σ' := ruled p rules)
      (fun _ _ => rfl) (fun _ _ => rfl) n
  rw [hheld] at hsilent
  -- The estimate.
  cases hread : rules.reading (w.host r)
      (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
        ++ [w.askedEvent r β]) r k with
  | none => exact Or.inl rfl
  | some s =>
    refine Or.inr ⟨s, rfl, ?_⟩
    by_cases hs0 : s < dueEdge p rules w lookahead q share nominal 0
    · exact Or.inl hs0
    · refine Or.inr ?_
      rw [not_lt] at hs0
      cases hc : ((ruled p rules : Solution H R Payload).followed u J).chosen w lookahead r k with
      | none =>
        -- The target is unknown: the covering block has not arrived.
        have hXnone := (hfol.none_iff k).mp hc
        rw [hX] at hXnone
        refine Or.inl ?_
        by_cases hcov : ∃ b, dueEdge p rules w lookahead q share nominal b ≤ s
            ∧ s < dueEdge p rules w lookahead q share nominal (b + 1)
        · obtain ⟨b, h1, h2⟩ := hcov
          refine ⟨b, h1, ?_⟩
          by_contra hlt
          rw [not_le] at hlt
          have := (hiff _).mpr ⟨s, b, hread, h1, h2, hlt, rfl⟩
          rw [hXnone] at this
          exact absurd this (by simp)
        · -- Every edge is at or before the estimate.
          have hall : ∀ b, dueEdge p rules w lookahead q share nominal b ≤ s := by
            intro b
            induction b with
            | zero => exact hs0
            | succ b ih =>
              by_contra hgt
              exact hcov ⟨b, ih, not_le.mp hgt⟩
          obtain ⟨b, hb⟩ := hK.handed ((w.speaker r).asked β)
          refine ⟨b, hall b, ?_⟩
          have hafter := w.network.after _ _ _ _ _
            (hK.noLoss.deliver w.sender (w.host r) (w.source.handed b) 0)
          linarith
      | some y =>
        -- The follower gives a position that cannot be played.
        have hXsome := hfol.target_of_some hc
        have hdist := hfol.dist_le huJ hc
        rw [hc] at hsilent
        cases hXk : (ruled p rules : Solution H R Payload).chosen w lookahead r k with
        | none =>
          rw [hXk] at hXsome
          exact absurd hXsome (by simp)
        | some x =>
          rw [hXk, Option.some.injEq] at hXsome
          rw [← hXsome] at hdist
          rw [hX] at hXk
          obtain ⟨s', b, hs', h1, h2, -, hx⟩ := (hiff x).mp hXk
          rw [hread, Option.some.injEq] at hs'
          subst hs'
          refine Or.inr ⟨b, x, h1, h2, hx, ?_⟩
          unfold playable at hsilent
          simp only at hsilent
          have hnot : ¬ (0 ≤ y ∧ ∀ m : ℕ, |(m : ℝ) - y| < (lookahead : ℕ) →
              m ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).held
                (w.host r)) := by
            intro hpl
            rw [ite_eq_left hpl] at hsilent
            exact absurd hsilent (by simp)
          have habs := abs_le.mp hdist
          by_cases hy0 : 0 ≤ y
          · right
            have hex : ∃ m : ℕ, |(m : ℝ) - y| < (lookahead : ℕ)
                ∧ m ∉ ((ruled p rules : Solution H R Payload).states w lookahead n).held
                  (w.host r) := by
              by_contra hno
              push Not at hno
              exact hnot ⟨hy0, hno⟩
            obtain ⟨m, hm1, hm2⟩ := hex
            obtain ⟨b', hb'⟩ := w.source.exists_block m
            refine ⟨b', ?_, ?_⟩
            · have h3 : (w.source.first b' : ℝ) ≤ m := by
                exact_mod_cast w.source.first_le_of_mem hb'
              have h4 := (abs_lt.mp hm1).2
              linarith [habs.2]
            · by_contra hlt
              rw [not_le] at hlt
              exact hm2 ((ruled_mem_held_iff hK.noLoss lookahead hr hE hb').mpr hlt)
          · left
            rw [not_le] at hy0
            linarith [habs.1]

end Unisono.Solutions.Controller
