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
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- What host `h` remembers after the events `l`. -/
abbrev memoryOf (h : H) (l : List (Event H R Payload)) : Memory H R :=
  l.foldl (remember p h) Memory.empty

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
      split at hb
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
        rw [h₀]
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
      simp only
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
    · split at ho
      · split_ifs at ho <;> exact keep ho
      · exact keep ho
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
      · split
        · split_ifs <;> exact ⟨a₀, θ₀, h₀, le_rfl⟩
        · exact ⟨a₀, θ₀, h₀, le_rfl⟩
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
    · split_ifs at ha <;> exact keep ha
    · split at ha
      · split_ifs at ha <;> exact keep ha
      · exact keep ha
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
    · split_ifs <;> rfl
    · split
      · split_ifs <;> rfl
      · rfl
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
    · split_ifs <;> rfl
    · split
      · split_ifs <;> rfl
      · rfl
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
    · split_ifs at ha <;> exact keep ha
    · split at ha
      · split_ifs at ha <;> exact keep ha
      · exact keep ha
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
      · split_ifs <;> exact ⟨a₀, h₀, le_rfl⟩
      · split
        · split_ifs <;> exact ⟨a₀, h₀, le_rfl⟩
        · exact ⟨a₀, h₀, le_rfl⟩
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
