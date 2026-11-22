/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay

/-!
# What the baseline remembers

Facts about the memory that a host of the baseline folds from the events of
its view (`memoryOf`), in any world.

* A host other than the sender's remembers a block that arrived, and no
  block that arrived is later (`block_received`, `block_latest`).
* It remembers a clock estimate from an answer that arrived, and no answer
  that arrived is to a later question (`offset_received`, `offset_latest`).
* The reading at which it last asked for the sender's clock is that of a
  device request at which it asked (`asked_request`).
* For each speaker, it remembers the position it chose for the last output
  sample of the speaker's last request (`last_after_request`, `last_none`).
* The sender remembers, for each host, the reading of a question of that
  host that it answered, and no question of that host that arrived is later
  (`answered_question`, `answered_latest`).
* For a block of consecutive output samples, the position a speaker chooses
  for each follows a recursion (`chosen`, `positions_block`): one step towards
  the target from the position chosen for the output sample before
  (`chosen_succ`, `chosen_zero_continues`), or the target when there is none
  (`chosen_zero_starts`); after the block, the speaker remembers the position
  chosen for its last output sample (`lastChosen_block`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- What host `h` remembers after the events `l`. -/
abbrev memoryOf (h : H) (l : List (Event H R Payload)) : Memory H R :=
  l.foldl (remember p h) Memory.empty

/-- The baseline acts on the last event of a view with what it remembers
from the events before. -/
theorem solution_append (h : H) (l : List (Event H R Payload)) (e : Event H R Payload) :
    (solution p : Solution H R Payload) h (l ++ [e]) = act p h (memoryOf p h l) e := by
  simp [solution, memoryOf]

/-- What a host remembers after one more event. -/
theorem memoryOf_append (h : H) (l : List (Event H R Payload)) (e : Event H R Payload) :
    memoryOf p h (l ++ [e]) = remember p h (memoryOf p h l) e := by
  simp [memoryOf, List.foldl_append]

/-- At a host other than the sender's, the block remembered is one that
arrived. -/
theorem block_received (h : H) (hh : h ≠ p.sender) (l : List (Event H R Payload)) {f : ℕ} {c : ℝ}
    (hb : (memoryOf p h l).block = some (f, c)) :
    ∃ e ∈ l, ∃ i F, e.observation = .received i (.block f c) F := by
  induction l using List.reverseRecOn generalizing f c with
  | nil => simp [memoryOf, Memory.empty] at hb
  | append_singleton l e ih =>
    rw [memoryOf_append] at hb
    have keep : (memoryOf p h l).block = some (f, c) →
        ∃ e' ∈ l ++ [e], ∃ i F, e'.observation = .received i (.block f c) F := by
      intro hb'
      obtain ⟨e', he', i, F, ho⟩ := ih hb'
      exact ⟨e', List.mem_append_left _ he', i, F, ho⟩
    unfold remember at hb
    split at hb
    · split_ifs at hb with hs
      · exact absurd hs hh
      · exact keep hb
    · rename_i i f' c' F ho
      split_ifs at hb with hs
      · exact absurd hs hh
      · split at hb
        · rename_i f'' c'' hold
          split_ifs at hb with hlt
          · simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), i, F, ho⟩
          · exact keep hb
        · simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), i, F, ho⟩
    · split_ifs at hb
      · exact keep hb
      · exact keep hb
    · split_ifs at hb
      · exact keep hb
      · split at hb <;> (try split_ifs at hb) <;> exact keep hb
    · exact keep hb
    · exact keep hb

/-- At a host other than the sender's, every block that arrived is no later
than the block remembered. -/
theorem block_latest (h : H) (hh : h ≠ p.sender) (l : List (Event H R Payload))
    {e : Event H R Payload} (he : e ∈ l) {i : H} {f : ℕ} {c : ℝ} {F : Finset ℕ}
    (ho : e.observation = .received i (.block f c) F) :
    ∃ f' c', (memoryOf p h l).block = some (f', c') ∧ f ≤ f' := by
  induction l using List.reverseRecOn with
  | nil => simp at he
  | append_singleton l e' ih =>
    rw [memoryOf_append]
    -- What the memory's block becomes after `e'`, given what it was.
    have step : ∀ f₀ c₀, (memoryOf p h l).block = some (f₀, c₀) →
        ∃ f' c', (remember p h (memoryOf p h l) e').block = some (f', c') ∧ f₀ ≤ f' := by
      intro f₀ c₀ h₀
      unfold remember
      split
      · split_ifs with hs
        · exact absurd hs hh
        · exact ⟨f₀, c₀, h₀, le_rfl⟩
      · rename_i i' f₁ c₁ F₁ ho₁
        split_ifs with hs
        · exact absurd hs hh
        · rw [h₀]
          simp only
          split_ifs with hlt
          · exact ⟨f₁, c₁, rfl, hlt.le⟩
          · exact ⟨f₀, c₀, h₀, le_rfl⟩
      · split_ifs <;> exact ⟨f₀, c₀, h₀, le_rfl⟩
      · split_ifs
        · exact ⟨f₀, c₀, h₀, le_rfl⟩
        · split <;> (try split_ifs) <;> exact ⟨f₀, c₀, h₀, le_rfl⟩
      · exact ⟨f₀, c₀, h₀, le_rfl⟩
      · exact ⟨f₀, c₀, h₀, le_rfl⟩
    rcases List.mem_append.mp he with he | he
    · obtain ⟨f₀, c₀, h₀, hle⟩ := ih he
      obtain ⟨f', c', h', hle'⟩ := step f₀ c₀ h₀
      exact ⟨f', c', h', hle.trans hle'⟩
    · rw [List.mem_singleton] at he
      subst he
      unfold remember
      rw [ho]
      simp only [hh, ↓reduceIte]
      split
      · rename_i f₀ c₀ h₀
        split_ifs with hlt
        · exact ⟨f, c, rfl, le_rfl⟩
        · exact ⟨f₀, c₀, h₀, not_lt.mp hlt⟩
      · exact ⟨f, c, rfl, le_rfl⟩

/-- At a host other than the sender's, the clock estimate remembered comes
from an answer that arrived: its question's reading `t₁`, and the estimate
from the sender's reading `t₂` and the reading at which the answer
arrived. -/
theorem offset_received (h : H) (hh : h ≠ p.sender) (l : List (Event H R Payload)) {t₁ θ : ℝ}
    (ho : (memoryOf p h l).offset = some (t₁, θ)) :
    ∃ e ∈ l, ∃ i t₂ F, e.observation = .received i (.answer t₁ t₂) F
      ∧ θ = t₂ - (t₁ + e.reading) / 2 := by
  induction l using List.reverseRecOn generalizing t₁ θ with
  | nil => simp [memoryOf, Memory.empty] at ho
  | append_singleton l e ih =>
    rw [memoryOf_append] at ho
    have keep : (memoryOf p h l).offset = some (t₁, θ) →
        ∃ e' ∈ l ++ [e], ∃ i t₂ F, e'.observation = .received i (.answer t₁ t₂) F
          ∧ θ = t₂ - (t₁ + e'.reading) / 2 := by
      intro ho'
      obtain ⟨e', he', i, t₂, F, ho₁, hθ⟩ := ih ho'
      exact ⟨e', List.mem_append_left _ he', i, t₂, F, ho₁, hθ⟩
    have here : ∀ i t₂ F, e.observation = .received i (.answer t₁ t₂) F →
        θ = t₂ - (t₁ + e.reading) / 2 →
        ∃ e' ∈ l ++ [e], ∃ i t₂ F, e'.observation = .received i (.answer t₁ t₂) F
          ∧ θ = t₂ - (t₁ + e'.reading) / 2 :=
      fun i t₂ F h1 h2 => ⟨e, List.mem_append_right _ (List.mem_singleton_self e), i, t₂, F, h1, h2⟩
    unfold remember at ho
    split at ho
    · split_ifs at ho with hs
      · exact absurd hs hh
      · exact keep ho
    · split_ifs at ho <;> (try split at ho) <;> (try split_ifs at ho) <;> exact keep ho
    · split_ifs at ho <;> exact keep ho
    · rename_i i sent received F hobs
      split_ifs at ho with hs
      · exact absurd hs hh
      · split at ho
        · split_ifs at ho with hlt
          · simp only [Option.some.injEq, Prod.mk.injEq] at ho
            obtain ⟨rfl, rfl⟩ := ho
            exact here i received F hobs rfl
          · exact keep ho
        · simp only [Option.some.injEq, Prod.mk.injEq] at ho
          obtain ⟨rfl, rfl⟩ := ho
          exact here i received F hobs rfl
    · exact keep ho
    · exact keep ho

/-- At a host other than the sender's, every answer that arrived carries a
question's reading no later than the one of the estimate remembered. -/
theorem offset_latest (h : H) (hh : h ≠ p.sender) (l : List (Event H R Payload))
    {e : Event H R Payload} (he : e ∈ l) {i : H} {t₁ t₂ : ℝ} {F : Finset ℕ}
    (ho : e.observation = .received i (.answer t₁ t₂) F) :
    ∃ t₁' θ, (memoryOf p h l).offset = some (t₁', θ) ∧ t₁ ≤ t₁' := by
  induction l using List.reverseRecOn with
  | nil => simp at he
  | append_singleton l e' ih =>
    rw [memoryOf_append]
    have step : ∀ a₀ θ₀, (memoryOf p h l).offset = some (a₀, θ₀) →
        ∃ t₁' θ, (remember p h (memoryOf p h l) e').offset = some (t₁', θ) ∧ a₀ ≤ t₁' := by
      intro a₀ θ₀ h₀
      unfold remember
      split
      · split_ifs with hs
        · exact absurd hs hh
        · exact ⟨a₀, θ₀, h₀, le_rfl⟩
      · split_ifs <;> (try split) <;> (try split_ifs) <;> exact ⟨a₀, θ₀, h₀, le_rfl⟩
      · split_ifs <;> exact ⟨a₀, θ₀, h₀, le_rfl⟩
      · split_ifs with hs
        · exact absurd hs hh
        · rw [h₀]
          simp only
          split_ifs with hlt
          · exact ⟨_, _, rfl, hlt.le⟩
          · exact ⟨a₀, θ₀, h₀, le_rfl⟩
      · exact ⟨a₀, θ₀, h₀, le_rfl⟩
      · exact ⟨a₀, θ₀, h₀, le_rfl⟩
    rcases List.mem_append.mp he with he | he
    · obtain ⟨a₀, θ₀, h₀, hle⟩ := ih he
      obtain ⟨t₁', θ, h', hle'⟩ := step a₀ θ₀ h₀
      exact ⟨t₁', θ, h', hle.trans hle'⟩
    · rw [List.mem_singleton] at he
      subst he
      unfold remember
      rw [ho]
      simp only
      split_ifs with hs
      · exact absurd hs hh
      · split
        · rename_i a₀ θ₀ h₀
          split_ifs with hlt
          · exact ⟨_, _, rfl, le_rfl⟩
          · exact ⟨a₀, θ₀, h₀, not_lt.mp hlt⟩
        · exact ⟨_, _, rfl, le_rfl⟩

/-- The reading at which a host last asked for the sender's clock is that of
a device request at which it asked, with what it remembered before it. -/
theorem asked_request (h : H) (l : List (Event H R Payload)) {a : ℝ}
    (ha : (memoryOf p h l).asked = some a) :
    ∃ l₁ e l₂, l = l₁ ++ e :: l₂ ∧ e.reading = a ∧ (∃ r outs st, e.observation = .asked r outs st)
      ∧ asks p h (memoryOf p h l₁) e.reading = true := by
  induction l using List.reverseRecOn generalizing a with
  | nil => simp [memoryOf, Memory.empty] at ha
  | append_singleton l e ih =>
    rw [memoryOf_append] at ha
    have keep : (memoryOf p h l).asked = some a →
        ∃ l₁ e' l₂, l ++ [e] = l₁ ++ e' :: l₂ ∧ e'.reading = a
          ∧ (∃ r outs st, e'.observation = .asked r outs st)
          ∧ asks p h (memoryOf p h l₁) e'.reading = true := by
      intro ha'
      obtain ⟨l₁, e', l₂, hl, h1, h2, h3⟩ := ih ha'
      exact ⟨l₁, e', l₂ ++ [e], by rw [hl]; simp, h1, h2, h3⟩
    unfold remember at ha
    split at ha
    · split_ifs at ha <;> (try split at ha) <;> exact keep ha
    · split_ifs at ha <;> (try split at ha) <;> (try split_ifs at ha) <;> exact keep ha
    · split_ifs at ha <;> exact keep ha
    · split_ifs at ha
      · exact keep ha
      · split at ha <;> (try split_ifs at ha) <;> exact keep ha
    · rename_i r outs st hobs
      simp only at ha
      split_ifs at ha with hask
      · simp only [Option.some.injEq] at ha
        exact ⟨l, e, [], rfl, ha, ⟨r, outs, st, hobs⟩, hask⟩
      · exact keep ha
    · exact keep ha

/-- After a device request of speaker `r`, and events that hold no other
request of `r`, a host remembers for `r` the position it chose for the
request's last output sample. -/
theorem last_after_request (h : H) (l₁ : List (Event H R Payload)) (e : Event H R Payload)
    (l₂ : List (Event H R Payload)) {r : Fin R} {outs : List ℕ} {st : ℝ}
    (he : e.observation = .asked r outs st)
    (hl₂ : ∀ e' ∈ l₂, ∀ outs' st', e'.observation ≠ .asked r outs' st') :
    (memoryOf p h (l₁ ++ e :: l₂)).last r
      = lastChosen (positions p (memoryOf p h l₁) r outs st) := by
  induction l₂ using List.reverseRecOn with
  | nil =>
    rw [show l₁ ++ [e] = l₁ ++ [e] from rfl, memoryOf_append]
    unfold remember
    rw [he]
    simp
  | append_singleton l₂ e' ih =>
    rw [show l₁ ++ e :: (l₂ ++ [e']) = (l₁ ++ e :: l₂) ++ [e'] by simp, memoryOf_append]
    have ih' := ih fun e'' he'' => hl₂ e'' (List.mem_append_left _ he'')
    have hne : ∀ outs' st', e'.observation ≠ .asked r outs' st' :=
      hl₂ e' (List.mem_append_right _ (List.mem_singleton_self e'))
    rw [← ih']
    unfold remember
    split
    · split_ifs <;> (try split) <;> rfl
    · split_ifs <;> (try split) <;> (try split_ifs) <;> rfl
    · split_ifs <;> rfl
    · split_ifs
      · rfl
      · split <;> (try split_ifs) <;> rfl
    · rename_i r' outs' st' hobs
      simp only
      have hr : r' ≠ r := by
        rintro rfl
        exact hne outs' st' hobs
      rw [Function.update_of_ne hr.symm]
    · rfl

/-- A host that has seen no request of speaker `r` remembers no position
for it. -/
theorem last_none (h : H) (l : List (Event H R Payload)) {r : Fin R}
    (hl : ∀ e ∈ l, ∀ outs st, e.observation ≠ .asked r outs st) :
    (memoryOf p h l).last r = none := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [memoryOf_append]
    have ih' := ih fun e' he' => hl e' (List.mem_append_left _ he')
    have hne : ∀ outs st, e.observation ≠ .asked r outs st :=
      hl e (List.mem_append_right _ (List.mem_singleton_self e))
    rw [← ih']
    unfold remember
    split
    · split_ifs <;> (try split) <;> rfl
    · split_ifs <;> (try split) <;> (try split_ifs) <;> rfl
    · split_ifs <;> rfl
    · split_ifs
      · rfl
      · split <;> (try split_ifs) <;> rfl
    · rename_i r' outs' st' hobs
      simp only
      have hr : r' ≠ r := by
        rintro rfl
        exact hne outs' st' hobs
      rw [Function.update_of_ne hr.symm]
    · rfl

/-- At the sender, the reading remembered as answered for host `i` is that of
a question of `i` that the sender answered, with what it remembered before
it. -/
theorem answered_question (l : List (Event H R Payload)) {i : H} {a : ℝ}
    (ha : (memoryOf p p.sender l).answered i = some a) :
    ∃ l₁ e l₂, l = l₁ ++ e :: l₂ ∧ (∃ F, e.observation = .received i (.ask a) F)
      ∧ answers (memoryOf p p.sender l₁) i a = true := by
  induction l using List.reverseRecOn generalizing a with
  | nil => simp [memoryOf, Memory.empty] at ha
  | append_singleton l e ih =>
    rw [memoryOf_append] at ha
    have keep : (memoryOf p p.sender l).answered i = some a →
        ∃ l₁ e' l₂, l ++ [e] = l₁ ++ e' :: l₂ ∧ (∃ F, e'.observation = .received i (.ask a) F)
          ∧ answers (memoryOf p p.sender l₁) i a = true := by
      intro ha'
      obtain ⟨l₁, e', l₂, hl, h1, h2⟩ := ih ha'
      exact ⟨l₁, e', l₂ ++ [e], by rw [hl]; simp, h1, h2⟩
    unfold remember at ha
    split at ha
    · split_ifs at ha <;> (try split at ha) <;> exact keep ha
    · split_ifs at ha <;> (try split at ha) <;> (try split_ifs at ha) <;> exact keep ha
    · rename_i i' sent F hobs
      split_ifs at ha with hans
      · by_cases hi : i' = i
        · subst hi
          simp only [Function.update_self, Option.some.injEq] at ha
          subst ha
          exact ⟨l, e, [], rfl, ⟨F, hobs⟩, hans.2⟩
        · simp only [Function.update_of_ne (Ne.symm hi)] at ha
          exact keep ha
      · exact keep ha
    · split_ifs at ha
      · exact keep ha
      · split at ha <;> (try split_ifs at ha) <;> exact keep ha
    · exact keep ha
    · exact keep ha

/-- At the sender, every question of host `i` that arrived carries a reading
no later than the one remembered as answered for `i`. -/
theorem answered_latest (l : List (Event H R Payload)) {e : Event H R Payload} (he : e ∈ l)
    {i : H} {sent : ℝ} {F : Finset ℕ} (ho : e.observation = .received i (.ask sent) F) :
    ∃ a, (memoryOf p p.sender l).answered i = some a ∧ sent ≤ a := by
  induction l using List.reverseRecOn with
  | nil => simp at he
  | append_singleton l e' ih =>
    rw [memoryOf_append]
    have step : ∀ a₀, (memoryOf p p.sender l).answered i = some a₀ →
        ∃ a, (remember p p.sender (memoryOf p p.sender l) e').answered i = some a ∧ a₀ ≤ a := by
      intro a₀ h₀
      unfold remember
      split
      · split_ifs <;> (try split) <;> exact ⟨a₀, h₀, le_rfl⟩
      · split_ifs <;> (try split) <;> (try split_ifs) <;> exact ⟨a₀, h₀, le_rfl⟩
      · rename_i i' sent' F' hobs
        split_ifs with hans
        · by_cases hi : i' = i
          · subst hi
            refine ⟨sent', Function.update_self .., ?_⟩
            have := hans.2
            simp only [answers, h₀, decide_eq_true_eq] at this
            exact this.le
          · exact ⟨a₀, by simp only [Function.update_of_ne (Ne.symm hi)]; exact h₀, le_rfl⟩
        · exact ⟨a₀, h₀, le_rfl⟩
      · split_ifs
        · exact ⟨a₀, h₀, le_rfl⟩
        · split <;> (try split_ifs) <;> exact ⟨a₀, h₀, le_rfl⟩
      · exact ⟨a₀, h₀, le_rfl⟩
      · exact ⟨a₀, h₀, le_rfl⟩
    rcases List.mem_append.mp he with he | he
    · obtain ⟨a₀, h₀, hle⟩ := ih he
      obtain ⟨a, h', hle'⟩ := step a₀ h₀
      exact ⟨a, h', hle.trans hle'⟩
    · rw [List.mem_singleton] at he
      subst he
      unfold remember
      rw [ho]
      simp only [true_and]
      split_ifs with hans
      · exact ⟨sent, Function.update_self .., le_rfl⟩
      · simp only [answers] at hans
        split at hans
        · rename_i a₀ h₀
          simp only [decide_eq_true_eq, not_lt] at hans
          exact ⟨a₀, h₀, hans⟩
        · simp at hans

end Unisono.Solutions.FixedDelay

namespace Unisono.Solutions.FixedDelay

variable {H : Type} {R : ℕ} (p : Params H)

/-- The position chosen for output sample `g + j` of a block whose output
samples start at `g`, when the output sample and position chosen last before
the block are `start`. -/
noncomputable def chosen (m : Memory H R) (first : ℕ) (stamp : ℝ) (start : Option (ℕ × ℝ)) (g : ℕ) :
    ℕ → Option ℝ
  | 0 => choose p m first stamp start g
  | j + 1 => choose p m first stamp ((chosen m first stamp start g j).map fun x => (g + j, x))
      (g + j + 1)

/-- The fold that chooses positions, over the output samples
`g, g + 1, …, g + i - 1`, gives each the position `chosen`, and ends with the
last of them. -/
theorem positions_fold (m : Memory H R) (first : ℕ) (stamp : ℝ) (start : Option (ℕ × ℝ))
    (g i : ℕ) :
    (List.range' g i).foldl
      (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ)) k =>
        let x := choose p m first stamp acc.2 k
        (acc.1 ++ [(k, x)], x.map fun x => (k, x))) ([], start)
      = ((List.range i).map fun j => (g + j, chosen p m first stamp start g j),
        if i = 0 then start
        else (chosen p m first stamp start g (i - 1)).map fun x => (g + (i - 1), x)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range'_concat, List.foldl_append, ih, List.range_succ, List.map_append]
    simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, Nat.add_sub_cancel,
      Nat.add_one_ne_zero, ite_false]
    rcases i with _ | i
    · simp [chosen]
    · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, chosen, one_mul, Nat.add_assoc]

/-- In the list of positions chosen for the output samples from `g`, output
sample `g + j` has the position chosen for it. -/
theorem lookup_chosen (v : ℕ → Option ℝ) (g i j : ℕ) (hj : j < i) :
    ((List.range i).map fun j => (g + j, v j)).lookup (g + j) = some (v j) := by
  induction i generalizing g j v with
  | zero => omega
  | succ i ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rcases j with _ | j
    · simp [List.lookup]
    · have hfun : ((fun j => (g + j, v j)) ∘ Nat.succ) = fun j => (g + 1 + j, v (j + 1)) := by
        funext k
        exact Prod.ext (by simp only [Function.comp, Nat.succ_eq_add_one]; ring) rfl
      rw [hfun]
      have h := ih (fun j => v (j + 1)) (g + 1) j (by omega)
      have hkey : (g + (j + 1) == g) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp only [List.lookup, Nat.add_zero, hkey]
      rw [show g + (j + 1) = g + 1 + j by ring]
      exact h

/-- For a block of output samples `g, g + 1, …, g + len - 1`, a speaker
chooses for output sample `g + j` the position `chosen` from the position it
chose last. -/
theorem positions_block (m : Memory H R) (r : Fin R) (stamp : ℝ) (g len : ℕ) :
    positions p m r (List.range' g len) stamp
      = (List.range len).map fun j => (g + j, chosen p m g stamp (m.last r) g j) := by
  rcases len with _ | len
  · simp [positions]
  · unfold positions
    have hhead : (List.range' g (len + 1)).headD 0 = g := by
      simp [List.range'_succ]
    rw [hhead, positions_fold]

/-- After a block of `len > 0` output samples from `g`, the output sample
and position chosen last are the last output sample of the block and the
position chosen for it. -/
theorem lastChosen_block (m : Memory H R) (r : Fin R) (stamp : ℝ) (g len : ℕ) (hlen : 0 < len) :
    lastChosen (positions p m r (List.range' g len) stamp)
      = (chosen p m g stamp (m.last r) g (len - 1)).map fun x => (g + (len - 1), x) := by
  rw [positions_block]
  obtain ⟨l, rfl⟩ : ∃ l, len = l + 1 := ⟨len - 1, by omega⟩
  rw [List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Nat.add_sub_cancel, lastChosen]
  cases chosen p m g stamp (m.last r) g l <;> rfl

/-- When the target of output sample `g + j + 1` is `goal` and the position
chosen for `g + j` is `x`, the position chosen for `g + j + 1` is one step
from `x` towards `goal`. -/
theorem chosen_succ (m : Memory H R) (first : ℕ) (stamp : ℝ) (start : Option (ℕ × ℝ)) (g j : ℕ)
    {x goal : ℝ} (hx : chosen p m first stamp start g j = some x)
    (hgoal : target p m first stamp (g + j + 1) = some goal) :
    chosen p m first stamp start g (j + 1) = some (advance p x goal) := by
  simp only [chosen, hx, Option.map_some, choose, hgoal, ite_true]

/-- When the target of output sample `g` is `goal` and the speaker chose `x`
for the output sample before, it chooses one step from `x` towards `goal`
for `g`. -/
theorem chosen_zero_continues (m : Memory H R) (first : ℕ) (stamp : ℝ) (g : ℕ) {x goal : ℝ}
    (hgoal : target p m first stamp (g + 1) = some goal) :
    chosen p m first stamp (some (g, x)) (g + 1) 0 = some (advance p x goal) := by
  simp only [chosen, choose, hgoal, ite_true]

/-- When the target of output sample `g` is `goal` and the speaker chose no
position before, it chooses `goal`. -/
theorem chosen_zero_starts (m : Memory H R) (first : ℕ) (stamp : ℝ) (g : ℕ) {goal : ℝ}
    (hgoal : target p m first stamp g = some goal) :
    chosen p m first stamp none g 0 = some goal := by
  simp only [chosen, choose, hgoal]

/-- When every output sample of a block has a target, the speaker chooses a
position for each of them. -/
theorem chosen_isSome (m : Memory H R) (first : ℕ) (stamp : ℝ) (start : Option (ℕ × ℝ)) (g : ℕ)
    (j : ℕ) (hgoal : ∀ i ≤ j, (target p m first stamp (g + i)).isSome) :
    (chosen p m first stamp start g j).isSome := by
  induction j with
  | zero =>
    obtain ⟨goal, hg⟩ := Option.isSome_iff_exists.mp (hgoal 0 le_rfl)
    simp only [Nat.add_zero] at hg
    simp only [chosen, choose, hg]
    split <;> (try split) <;> simp_all
  | succ j ih =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ih fun i hi => hgoal i (by omega))
    obtain ⟨goal, hg⟩ := Option.isSome_iff_exists.mp (hgoal (j + 1) le_rfl)
    rw [show g + (j + 1) = g + j + 1 by ring] at hg
    rw [chosen_succ p m first stamp start g j hx hg]
    rfl

end Unisono.Solutions.FixedDelay
