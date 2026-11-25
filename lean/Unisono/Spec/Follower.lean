/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Limiter

/-!
# A follower: playback that moves toward what a solution chooses

`Unisono.Spec.Limiter` passes the positions that a solution chooses through
a limiter, which plays nothing where a step would break the step bound. This
file does the same for any rule that turns the value given to the previous
output sample and the position that the solution chooses into the value of
this output sample, and then defines one such rule, the follower.

* `stepAt`, `stepLast`, `carried`, `Solution.stepped`: the solution `σ`
  with a rule `g`. It sends what `σ` sends. At each request of a playback
  device, output sample by output sample, it gives the rule the value of the
  previous output sample and the position that `σ` chooses. The value of the
  last output sample of a block is carried to the next request of the same
  speaker by a fold over the host's view.
* `Solution.stepped_views`, `Solution.stepped_chosenAt_succ`: its run has
  the views of the run of `σ`, and what it chooses for an output sample is
  the rule's step from what it chose for the output sample before.
* `followStep`: the follower. When the position that `σ` chooses is one
  frame after the previous value within `u`, the follower takes it. When it
  is further, but within `J` frames, the follower advances by one frame
  moved by `u` toward it. When it is further than that, the follower jumps
  to it. With `J ≥ 1` such a jump is not a step of continuous playback.
* `Solution.followed_withinStep`: so the solution with the follower keeps
  the step bound `u` in every world, for `u ≥ 0` and `J ≥ 1`: in every step
  of continuous playback its position advances by one frame within `u`.

The follower never plays nothing where the solution chooses a position, and
it does not need the solution's positions to respect any bound. How close
it stays to what the solution chooses is not stated here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

/-! ## The output samples of one block -/

/-- The value that the rule gives output sample `k`, when it is given
`prev` before the output samples of the list and the solution chooses
`f j` for output sample `j`. Nothing if `k` is not in the list. -/
def stepAt (g : Option ℝ → Option ℝ → Option ℝ) (f : ℕ → Option ℝ) :
    Option ℝ → List ℕ → ℕ → Option ℝ
  | _, [], _ => none
  | prev, j :: js, k =>
      if k = j then g prev (f j) else stepAt g f (g prev (f j)) js k

/-- The value that the rule gives the last output sample of the list, or
`prev` if the list is empty. -/
def stepLast (g : Option ℝ → Option ℝ → Option ℝ) (f : ℕ → Option ℝ) : Option ℝ → List ℕ → Option ℝ
  | prev, [] => prev
  | prev, j :: js => stepLast g f (g prev (f j)) js

/-- The rule at the first of consecutive output samples. -/
theorem stepAt_range'_first (g : Option ℝ → Option ℝ → Option ℝ) (f : ℕ → Option ℝ)
    (prev : Option ℝ) (a n : ℕ) :
    stepAt g f prev (List.range' a (n + 1)) a = g prev (f a) := by
  simp [List.range'_succ, stepAt]

/-- The rule at consecutive output samples: each is given the value of
the one before it. -/
theorem stepAt_range'_succ (g : Option ℝ → Option ℝ → Option ℝ) (f : ℕ → Option ℝ) :
    ∀ (n a : ℕ) (prev : Option ℝ) (k : ℕ), a ≤ k → k + 1 < a + n →
      stepAt g f prev (List.range' a n) (k + 1)
        = g (stepAt g f prev (List.range' a n) k) (f (k + 1))
  | 0, a, _, k, h1, h2 => by omega
  | n + 1, a, prev, k, h1, h2 => by
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [stepAt_range'_first]
        simp [List.range'_succ, stepAt]
      · have ih := stepAt_range'_succ g f n (a + 1) (g prev (f a)) k (by omega)
          (by omega)
        have hk : k ≠ a := by omega
        have hk1 : k + 1 ≠ a := by omega
        simp only [List.range'_succ, stepAt, ite_eq_right hk, ite_eq_right hk1]
        exact ih

/-- After consecutive output samples the rule holds the value of the last
of them. -/
theorem stepLast_range' (g : Option ℝ → Option ℝ → Option ℝ) (f : ℕ → Option ℝ) :
    ∀ (n a : ℕ) (prev : Option ℝ),
      stepLast g f prev (List.range' a (n + 1)) = stepAt g f prev (List.range' a (n + 1)) (a + n)
  | 0, a, prev => by simp [List.range'_succ, stepAt, stepLast]
  | n + 1, a, prev => by
      have ih := stepLast_range' g f n (a + 1) (g prev (f a))
      have hne : a + (n + 1) ≠ a := by omega
      have e : a + 1 + n = a + (n + 1) := by omega
      rw [List.range'_succ, stepLast, stepAt, ite_eq_right hne, ih, e]

/-! ## The value that is carried across blocks -/

/-- One event of a host's view, for the rule: the view so far, and for
each speaker the value that the rule gave its last output sample. A
request of a playback device moves the rule over the output samples of
the block. -/
def carryStep (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) (h : H)
    (acc : List (Event H R Msg) × (Fin R → Option ℝ)) (e : Event H R Msg) :
    List (Event H R Msg) × (Fin R → Option ℝ) :=
  (acc.1 ++ [e],
    match e.observation with
    | .asked r outputs _ =>
        Function.update acc.2 r (stepLast g (σ h (acc.1 ++ [e])).plays (acc.2 r) outputs)
    | _ => acc.2)

/-- For each speaker, the value that the rule gave its last output
sample, after the events `l` of the view of host `h`. -/
def carried (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) (h : H)
    (l : List (Event H R Msg)) : Fin R → Option ℝ :=
  (l.foldl (carryStep σ g h) ([], fun _ => none)).2

theorem foldl_carryStep_fst (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) (h : H) :
    ∀ (l : List (Event H R Msg)) (acc : List (Event H R Msg) × (Fin R → Option ℝ)),
      (l.foldl (carryStep σ g h) acc).1 = acc.1 ++ l
  | [], acc => by simp
  | e :: l, acc => by
      rw [List.foldl_cons, foldl_carryStep_fst σ g h l]
      simp [carryStep]

/-- After the request of a block, the rule remembers the value of the
block's last output sample. -/
theorem carried_concat_asked (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) (h : H)
    (l : List (Event H R Msg)) (c : ℝ) (r : Fin R) (outputs : List ℕ) (s : ℝ) :
    carried σ g h (l ++ [⟨c, .asked r outputs s⟩]) r
      = stepLast g (σ h (l ++ [⟨c, .asked r outputs s⟩])).plays (carried σ g h l r)
          outputs := by
  unfold carried
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [carryStep]
  rw [foldl_carryStep_fst, List.nil_append, Function.update_self]

/-- An event that is not a request of speaker `r` leaves what the rule
remembers for `r`. -/
theorem carried_concat_of_ne (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) (h : H)
    (l : List (Event H R Msg)) (e : Event H R Msg) (r : Fin R)
    (hne : ∀ outputs s, e.observation ≠ .asked r outputs s) :
    carried σ g h (l ++ [e]) r = carried σ g h l r := by
  unfold carried
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [carryStep]
  cases hobs : e.observation with
  | asked r' outputs s =>
    have hr : r ≠ r' := by
      rintro rfl
      exact hne outputs s hobs
    simp only [Function.update_of_ne hr]
  | handed frames stamp => rfl
  | received j c F => rfl
  | timer => rfl

/-- Events none of which is a request of speaker `r` leave what the rule
remembers for `r`. -/
theorem carried_append_of_ne (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) (h : H)
    (l : List (Event H R Msg)) (r : Fin R) :
    ∀ l' : List (Event H R Msg), (∀ e ∈ l', ∀ outputs s, e.observation ≠ .asked r outputs s) →
      carried σ g h (l ++ l') r = carried σ g h l r := by
  intro l'
  induction l' using List.reverseRecOn with
  | nil => intro _; rw [List.append_nil]
  | append_singleton l' e ih =>
    intro hne
    rw [← List.append_assoc, carried_concat_of_ne σ g h (l ++ l') e r
      (hne e (by simp))]
    exact ih fun e' he' => hne e' (List.mem_append_left _ he')

/-! ## The solution with a rule -/

/-- The solution `σ` with the rule: the same messages and timers, and at
each request of a playback device the positions that `σ` chooses, passed
through the rule. -/
def Solution.stepped (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ) :
    Solution H R Msg := fun h view =>
  { sends := (σ h view).sends
    timers := (σ h view).timers
    plays :=
      match view.getLast? with
      | some e =>
          match e.observation with
          | .asked r outputs _ =>
              stepAt g (σ h view).plays (carried σ g h view.dropLast r) outputs
          | _ => (σ h view).plays
      | none => (σ h view).plays }

/-- What the solution with the rule chooses at a request of a playback device. -/
theorem Solution.stepped_plays_asked (σ : Solution H R Msg)
    (g : Option ℝ → Option ℝ → Option ℝ) (h : H) (l : List (Event H R Msg)) (c : ℝ)
    (r : Fin R) (outputs : List ℕ) (s : ℝ) :
    ((σ.stepped g) h (l ++ [⟨c, .asked r outputs s⟩])).plays
      = stepAt g (σ h (l ++ [⟨c, .asked r outputs s⟩])).plays (carried σ g h l r)
          outputs := by
  simp [Solution.stepped]


/-! ## The run of the solution with a rule -/

section Run

variable [DecidableEq H] (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ)
  (w : World H R) (lookahead : ℕ+)

/-- **What the rule remembers at the next request.** Let step `n₁` of the
run of `σ` handle the request of block `b` of speaker `r`, and let the
speaker's next request at a later step `n₂` be that of block `b + 1`. Then
at step `n₂` the rule of any solution `τ`, run over the view of the
speaker's host, remembers the value that it gave the last output sample of
block `b`. -/
theorem Solution.carried_at_next (τ : Solution H R Msg) {n₁ n₂ : ℕ} {r : Fin R} {b : ℕ}
    (hb₁ : (σ.states w lookahead n₁).askedNext r = b)
    (he₁ : earliest ((σ.states w lookahead n₁).key w) (σ.states w lookahead n₁).due
      = some (.asked r b))
    (hlt : n₁ < n₂) (hb₂ : (σ.states w lookahead n₂).askedNext r = b + 1) :
    carried τ g (w.host r) ((σ.states w lookahead n₂).views (w.host r)) r
      = stepLast g
          (τ (w.host r) ((σ.states w lookahead n₁).views (w.host r) ++ [w.askedEvent r b])).plays
          (carried τ g (w.host r) ((σ.states w lookahead n₁).views (w.host r)) r)
          ((w.speaker r).block b) := by
  have hhandled := σ.handled_of_asked w lookahead he₁
  have hview₁ : (σ.states w lookahead (n₁ + 1)).views (w.host r)
      = (σ.states w lookahead n₁).views (w.host r) ++ [w.askedEvent r b] := by
    rw [σ.views_succ w lookahead n₁ (w.host r), hhandled]
    simp [World.askedEvent]
  obtain ⟨l', hl', hev⟩ := σ.views_append w lookahead (Nat.succ_le_of_lt hlt) (w.host r)
  have hnext : (σ.states w lookahead (n₁ + 1)).askedNext r = b + 1 := by
    have h1 := σ.askedNext_succ w lookahead (n := n₁) (r := r) (by rw [hb₁]; exact he₁)
    rw [h1, hb₁]
  have hne : ∀ e ∈ l', ∀ outputs s, e.observation ≠ .asked r outputs s := by
    intro e he outputs s hobs
    obtain ⟨i, hi₁, hi₂, t, obs, hh, rfl⟩ := hev e he
    dsimp only at hobs
    subst hobs
    exact σ.no_request_between w lookahead (hnext.trans hb₂.symm) hi₁ hi₂ hh
  rw [hl', hview₁, carried_append_of_ne τ g (w.host r) _ r l' hne]
  exact carried_concat_asked τ g (w.host r) _ _ r _ _

/-- The solution with the rule and the solution have the same views. -/
theorem Solution.stepped_views (n : ℕ) :
    ((σ.stepped g).states w lookahead n).views = (σ.states w lookahead n).views :=
  Solution.views_eq_of_sends_eq w lookahead (σ := σ.stepped g) (σ' := σ) (fun _ _ => rfl)
    (fun _ _ => rfl) n

/-- The solution with the rule and the solution handle the requests of the
playback devices at the same steps. -/
theorem Solution.stepped_asked_iff (n : ℕ) (r : Fin R) (b : ℕ) :
    (((σ.stepped g).states w lookahead n).askedNext r = b
      ∧ earliest (((σ.stepped g).states w lookahead n).key w)
          ((σ.stepped g).states w lookahead n).due = some (.asked r b))
    ↔ ((σ.states w lookahead n).askedNext r = b
      ∧ earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
          = some (.asked r b)) := by
  have h1 := Solution.askedNext_eq_of_sends_eq w lookahead (σ := σ.stepped g) (σ' := σ)
    (fun _ _ => rfl) (fun _ _ => rfl) n
  have h2 := (Solution.earliest_eq_of_sends_eq w lookahead (σ := σ.stepped g) (σ' := σ)
    (fun _ _ => rfl) (fun _ _ => rfl) n).2
  rw [h1, h2]

/-- **What the solution with the rule chooses at a request**: the positions that
the solution chooses there, passed through the rule, which starts from
the value that it remembers for the speaker. -/
theorem Solution.stepped_chosenAt (n : ℕ) (r : Fin R) (b k : ℕ) :
    (σ.stepped g).chosenAt w lookahead n r b k
      = stepAt g (σ.chosenAt w lookahead n r b)
          (carried σ g (w.host r) ((σ.states w lookahead n).views (w.host r)) r)
          ((w.speaker r).block b) k := by
  unfold Solution.chosenAt
  rw [σ.stepped_views g w lookahead n]
  unfold World.askedEvent
  rw [Solution.stepped_plays_asked]

/-- **The rule runs on from one output sample to the next**, within a
block and from the last output sample of a block to the first of the next.
Let step `n₁` of the run of `σ` handle the request of the block that holds
output sample `k` of speaker `r`, and step `n₂` that of the block that holds
`k + 1`. What the solution with the rule chooses for `k + 1` is the rule's step
from what it chooses for `k` and what `σ` chooses for `k + 1`. -/
theorem Solution.stepped_chosenAt_succ {n₁ n₂ b₁ b₂ k : ℕ} {r : Fin R}
    (hb₁ : (σ.states w lookahead n₁).askedNext r = b₁)
    (he₁ : earliest ((σ.states w lookahead n₁).key w) (σ.states w lookahead n₁).due
      = some (.asked r b₁))
    (hk₁ : k ∈ (w.speaker r).block b₁)
    (hb₂ : (σ.states w lookahead n₂).askedNext r = b₂)
    (he₂ : earliest ((σ.states w lookahead n₂).key w) (σ.states w lookahead n₂).due
      = some (.asked r b₂))
    (hk₂ : k + 1 ∈ (w.speaker r).block b₂) :
    (σ.stepped g).chosenAt w lookahead n₂ r b₂ (k + 1)
      = g ((σ.stepped g).chosenAt w lookahead n₁ r b₁ k)
          (σ.chosenAt w lookahead n₂ r b₂ (k + 1)) := by
  have hmono := (w.speaker r).first_strictMono
  have hr₁ : (w.speaker r).first b₁ ≤ k ∧ k < (w.speaker r).first (b₁ + 1) := by
    have h := hk₁
    unfold PlaybackDevice.block at h
    rw [List.mem_range'_1] at h
    have := hmono (Nat.lt_add_one b₁)
    omega
  have hr₂ : (w.speaker r).first b₂ ≤ k + 1 ∧ k + 1 < (w.speaker r).first (b₂ + 1) := by
    have h := hk₂
    unfold PlaybackDevice.block at h
    rw [List.mem_range'_1] at h
    have := hmono (Nat.lt_add_one b₂)
    omega
  rw [σ.stepped_chosenAt g w lookahead n₂ r b₂ (k + 1),
    σ.stepped_chosenAt g w lookahead n₁ r b₁ k]
  by_cases hbb : b₁ = b₂
  · subst hbb
    obtain rfl := σ.asked_step_unique w lookahead hb₁ he₁ hb₂ he₂
    unfold PlaybackDevice.block
    exact stepAt_range'_succ g _ _ _ _ k hr₁.1 (by omega)
  · -- The two output samples are in consecutive blocks.
    have h12 : b₁ ≤ b₂ := by
      by_contra hlt
      have := hmono.monotone (show b₂ + 1 ≤ b₁ by omega)
      omega
    have h21 : b₂ ≤ b₁ + 1 := by
      by_contra hlt
      have := hmono.monotone (show b₁ + 1 + 1 ≤ b₂ by omega)
      have := hmono (Nat.lt_add_one (b₁ + 1))
      omega
    obtain rfl : b₂ = b₁ + 1 := by omega
    have hfirst : (w.speaker r).first (b₁ + 1) = k + 1 := by omega
    have hn : n₁ < n₂ := by
      by_contra hge
      have := Solution.askedNext_mono w σ lookahead r (not_lt.mp hge)
      simp only at this
      omega
    rw [σ.carried_at_next g w lookahead σ hb₁ he₁ hn hb₂]
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, (w.speaker r).first (b₁ + 1) - (w.speaker r).first b₁ = c₁ + 1 :=
      ⟨(w.speaker r).first (b₁ + 1) - (w.speaker r).first b₁ - 1, by
        have := hmono (Nat.lt_add_one b₁)
        omega⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c₂,
        (w.speaker r).first (b₁ + 1 + 1) - (w.speaker r).first (b₁ + 1) = c₂ + 1 :=
      ⟨(w.speaker r).first (b₁ + 1 + 1) - (w.speaker r).first (b₁ + 1) - 1, by
        have := hmono (Nat.lt_add_one (b₁ + 1))
        omega⟩
    have hk : (w.speaker r).first b₁ + c₁ = k := by omega
    unfold PlaybackDevice.block
    rw [hc₁, hc₂, stepLast_range', hk, hfirst, stepAt_range'_first]
    rfl

end Run

/-! ## The follower -/

/-- **One step of the follower.** Given the value `y` of the previous output
sample and the position `x` that the solution chooses: `x` itself when it
is one frame after `y` within `u`; otherwise, when it is within `J` frames
of one frame after `y`, the position one frame after `y` moved by `u`
toward `x`; otherwise `x`, a jump. With no previous value the follower
takes what the solution chooses, and where the solution chooses nothing the
follower gives nothing. -/
def followStep (u J : ℝ) : Option ℝ → Option ℝ → Option ℝ
  | some y, some x =>
      if |x - y - 1| ≤ u then some x
      else if |x - y - 1| ≤ J then some (y + 1 + if y + 1 < x then u else -u)
      else some x
  | _, x => x

/-- The follower takes a position that is one frame after the previous
value within `u`. -/
theorem followStep_of_within {u J y x : ℝ} (h : |x - y - 1| ≤ u) :
    followStep u J (some y) (some x) = some x := by
  simp only [followStep]
  rw [ite_eq_left h]

/-- **A step of continuous playback of the follower is within the bound.**
For `u ≥ 0` and `J ≥ 1`: if the follower gives `z` after `y`, with
`y < z < y + 2`, then `z` is one frame after `y` within `u`. -/
theorem followStep_within {u J y z : ℝ} (hu : 0 ≤ u) (hJ : 1 ≤ J) {x : Option ℝ}
    (h : followStep u J (some y) x = some z) (h1 : y < z) (h2 : z < y + 2) :
    |z - y - 1| ≤ u := by
  rcases x with _ | x
  · simp [followStep] at h
  · simp only [followStep] at h
    by_cases h3 : |x - y - 1| ≤ u
    · rw [ite_eq_left h3] at h
      obtain rfl := Option.some.inj h
      exact h3
    · rw [ite_eq_right h3] at h
      by_cases h4 : |x - y - 1| ≤ J
      · rw [ite_eq_left h4] at h
        obtain rfl := Option.some.inj h
        by_cases h5 : y + 1 < x
        · rw [ite_eq_left h5, show y + 1 + u - y - 1 = u from by ring, abs_of_nonneg hu]
        · rw [ite_eq_right h5, show y + 1 + -u - y - 1 = -u from by ring, abs_neg,
            abs_of_nonneg hu]
      · rw [ite_eq_right h4] at h
        obtain rfl := Option.some.inj h
        exfalso
        have h5 : |x - y - 1| < 1 := by
          rw [abs_lt]
          constructor <;> linarith
        linarith [not_le.mp h4]

/-- **The solution `σ` with the follower**: the same messages and timers,
and at each request of a playback device the positions that `σ` chooses,
followed within the step bound `u`, with jumps beyond `J` frames. -/
def Solution.followed (σ : Solution H R Msg) (u J : ℝ) : Solution H R Msg :=
  σ.stepped (followStep u J)

/-- **The solution with the follower keeps the step bound**, in every
world, for `u ≥ 0` and `J ≥ 1`: in every step of continuous playback its
position advances by one frame per output sample within `u`. -/
theorem Solution.followed_withinStep [DecidableEq H] (σ : Solution H R Msg) {u J : ℝ}
    (hu : 0 ≤ u) (hJ : 1 ≤ J) (w : World H R) (lookahead : ℕ+) :
    (σ.followed u J).WithinStep w lookahead u := by
  intro r k x y hx hy hxy hyx
  obtain ⟨b₁, n₁, hk₁, hb₁, he₁, hc₁⟩ :=
    exists_asked_of_plays_some (σ.stepped (followStep u J)) w lookahead hx
  obtain ⟨b₂, n₂, hk₂, hb₂, he₂, hc₂⟩ :=
    exists_asked_of_plays_some (σ.stepped (followStep u J)) w lookahead hy
  obtain ⟨hb₁', he₁'⟩ :=
    (σ.stepped_asked_iff (followStep u J) w lookahead n₁ r b₁).mp ⟨hb₁, he₁⟩
  obtain ⟨hb₂', he₂'⟩ :=
    (σ.stepped_asked_iff (followStep u J) w lookahead n₂ r b₂).mp ⟨hb₂, he₂⟩
  have hchain := σ.stepped_chosenAt_succ (followStep u J) w lookahead hb₁' he₁' hk₁ hb₂' he₂'
    hk₂
  have h1 : (σ.stepped (followStep u J)).chosenAt w lookahead n₁ r b₁ k = some x := hc₁
  have h2 : (σ.stepped (followStep u J)).chosenAt w lookahead n₂ r b₂ (k + 1) = some y := hc₂
  rw [h1, h2] at hchain
  exact followStep_within hu hJ hchain.symm hxy hyx

/-- The solution with a rule sends what the solution sends, so it is a star
solution when the solution is one. -/
theorem Solution.stepped_isStar (σ : Solution H R Msg) (g : Option ℝ → Option ℝ → Option ℝ)
    {s : H} (hσ : σ.IsStar s) : (σ.stepped g).IsStar s :=
  fun h view dst msg frames hmem => hσ h view dst msg frames hmem

end Unisono.Spec
