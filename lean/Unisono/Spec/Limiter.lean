/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Limits
public import Unisono.Spec.SameMessages

/-!
# A limiter that makes any solution keep the speed bound

The speed bound (`Solution.WithinStep`) asks that the played position
advance by one frame per output sample within `u`, in every step of
continuous playback. This file turns any solution into one that keeps the
bound in every world.

The limited solution (`Solution.limited`) sends the same messages and sets
the same timers. At each output sample it plays the position that the
solution chooses, except when the step from the position chosen at the
previous output sample would be a step of continuous playback outside the
bound: then it plays nothing of the source at that output sample
(`limitStep`). After an output sample that plays nothing, the next one is
free. The limiter remembers the last value across the blocks of a playback
device; a host recomputes it from its view (`limiterLast`).

* `Solution.limited_withinStep`: the limited solution keeps the speed bound
  `u` in every world.
* `Solution.limited_plays_eq_some`: whatever the limited solution plays at
  an output sample, the solution plays there too.
* `Solution.limited_plays_eq`: if, from some output sample on, the positions
  that the solution chooses for a speaker are on a line whose slope is
  within `u` of one, or are nothing, then from the next output sample on the
  limited solution plays what the solution plays.

The run of the limited solution is the run of the solution apart from what
the speakers play (`Unisono.Spec.SameMessages`). The limiter is applied to
the controller in `Unisono.Solutions.Controller.Limited`.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

/-! ## One step of the limiter -/

/-- The limiter at one output sample: given what the previous output sample
was given, `prev`, and the position `y` that the solution chooses, the
position that is played. It is `y`, except when the previous value is a
position `x` and the step from `x` to `y` is a step of continuous playback
that advances by one frame outside `u`: then nothing is played. -/
def limitStep (u : ℝ) : Option ℝ → Option ℝ → Option ℝ
  | some x, some y => if x < y ∧ y < x + 2 ∧ u < |y - x - 1| then none else some y
  | _, y => y

theorem limitStep_none_left (u : ℝ) (y : Option ℝ) : limitStep u none y = y := by
  cases y <;> rfl

theorem limitStep_none_right (u : ℝ) (prev : Option ℝ) : limitStep u prev none = none := by
  cases prev <;> rfl

/-- What the limiter lets through is what the solution chose. -/
theorem limitStep_eq_some {u : ℝ} {prev y : Option ℝ} {z : ℝ}
    (h : limitStep u prev y = some z) : y = some z := by
  rcases prev with _ | x <;> rcases y with _ | y'
  · simp [limitStep] at h
  · simpa [limitStep] using h
  · simp [limitStep] at h
  · simp only [limitStep] at h
    split_ifs at h
    exact h

/-- A step of continuous playback that the limiter lets through is within
the bound. -/
theorem limitStep_within {u x z : ℝ} {y : Option ℝ} (h : limitStep u (some x) y = some z)
    (h1 : x < z) (h2 : z < x + 2) : |z - x - 1| ≤ u := by
  rcases y with _ | y'
  · simp [limitStep] at h
  · simp only [limitStep] at h
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    by_contra hlt
    exact hc ⟨h1, h2, not_le.mp hlt⟩

/-- The limiter lets a step within the bound through. -/
theorem limitStep_of_within {u x y : ℝ} (h : x < y → y < x + 2 → |y - x - 1| ≤ u) :
    limitStep u (some x) (some y) = some y := by
  simp only [limitStep]
  rw [ite_eq_right]
  rintro ⟨h1, h2, h3⟩
  exact absurd (h h1 h2) (not_le.mpr h3)

/-! ## The output samples of one block -/

/-- The value that the limiter gives output sample `k`, when it is given
`prev` before the output samples of the list and the solution chooses
`f j` for output sample `j`. Nothing if `k` is not in the list. -/
def limitAt (u : ℝ) (f : ℕ → Option ℝ) : Option ℝ → List ℕ → ℕ → Option ℝ
  | _, [], _ => none
  | prev, j :: js, k =>
      if k = j then limitStep u prev (f j) else limitAt u f (limitStep u prev (f j)) js k

/-- The value that the limiter gives the last output sample of the list, or
`prev` if the list is empty. -/
def limitLast (u : ℝ) (f : ℕ → Option ℝ) : Option ℝ → List ℕ → Option ℝ
  | prev, [] => prev
  | prev, j :: js => limitLast u f (limitStep u prev (f j)) js

theorem limitAt_eq_some {u : ℝ} {f : ℕ → Option ℝ} {z : ℝ} :
    ∀ {l : List ℕ} {prev : Option ℝ} {k : ℕ}, limitAt u f prev l k = some z → f k = some z
  | [], _, _, h => by simp [limitAt] at h
  | j :: js, prev, k, h => by
      simp only [limitAt] at h
      split_ifs at h with hk
      · rw [hk]
        exact limitStep_eq_some h
      · exact limitAt_eq_some h

/-- The limiter at the first of consecutive output samples. -/
theorem limitAt_range'_first (u : ℝ) (f : ℕ → Option ℝ) (prev : Option ℝ) (a n : ℕ) :
    limitAt u f prev (List.range' a (n + 1)) a = limitStep u prev (f a) := by
  simp [List.range'_succ, limitAt]

/-- The limiter at consecutive output samples: each is given the value of
the one before it. -/
theorem limitAt_range'_succ (u : ℝ) (f : ℕ → Option ℝ) :
    ∀ (n a : ℕ) (prev : Option ℝ) (k : ℕ), a ≤ k → k + 1 < a + n →
      limitAt u f prev (List.range' a n) (k + 1)
        = limitStep u (limitAt u f prev (List.range' a n) k) (f (k + 1))
  | 0, a, _, k, h1, h2 => by omega
  | n + 1, a, prev, k, h1, h2 => by
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [limitAt_range'_first]
        simp [List.range'_succ, limitAt]
      · have ih := limitAt_range'_succ u f n (a + 1) (limitStep u prev (f a)) k (by omega)
          (by omega)
        have hk : k ≠ a := by omega
        have hk1 : k + 1 ≠ a := by omega
        simp only [List.range'_succ, limitAt, ite_eq_right hk, ite_eq_right hk1]
        exact ih

/-- After consecutive output samples the limiter holds the value of the last
of them. -/
theorem limitLast_range' (u : ℝ) (f : ℕ → Option ℝ) :
    ∀ (n a : ℕ) (prev : Option ℝ),
      limitLast u f prev (List.range' a (n + 1)) = limitAt u f prev (List.range' a (n + 1)) (a + n)
  | 0, a, prev => by simp [List.range'_succ, limitAt, limitLast]
  | n + 1, a, prev => by
      have ih := limitLast_range' u f n (a + 1) (limitStep u prev (f a))
      have hne : a + (n + 1) ≠ a := by omega
      have e : a + 1 + n = a + (n + 1) := by omega
      rw [List.range'_succ, limitLast, limitAt, ite_eq_right hne, ih, e]

/-! ## The value that the limiter remembers across blocks -/

/-- One event of a host's view, for the limiter: the view so far, and for
each speaker the value that the limiter gave its last output sample. A
request of a playback device moves the limiter over the output samples of
the block. -/
def limiterStep (σ : Solution H R Msg) (u : ℝ) (h : H)
    (acc : List (Event H R Msg) × (Fin R → Option ℝ)) (e : Event H R Msg) :
    List (Event H R Msg) × (Fin R → Option ℝ) :=
  (acc.1 ++ [e],
    match e.observation with
    | .asked r outputs _ =>
        Function.update acc.2 r (limitLast u (σ h (acc.1 ++ [e])).plays (acc.2 r) outputs)
    | _ => acc.2)

/-- For each speaker, the value that the limiter gave its last output
sample, after the events `l` of the view of host `h`. -/
def limiterLast (σ : Solution H R Msg) (u : ℝ) (h : H) (l : List (Event H R Msg)) :
    Fin R → Option ℝ :=
  (l.foldl (limiterStep σ u h) ([], fun _ => none)).2

theorem foldl_limiterStep_fst (σ : Solution H R Msg) (u : ℝ) (h : H) :
    ∀ (l : List (Event H R Msg)) (acc : List (Event H R Msg) × (Fin R → Option ℝ)),
      (l.foldl (limiterStep σ u h) acc).1 = acc.1 ++ l
  | [], acc => by simp
  | e :: l, acc => by
      rw [List.foldl_cons, foldl_limiterStep_fst σ u h l]
      simp [limiterStep]

/-- After the request of a block, the limiter remembers the value of the
block's last output sample. -/
theorem limiterLast_concat_asked (σ : Solution H R Msg) (u : ℝ) (h : H)
    (l : List (Event H R Msg)) (c : ℝ) (r : Fin R) (outputs : List ℕ) (s : ℝ) :
    limiterLast σ u h (l ++ [⟨c, .asked r outputs s⟩]) r
      = limitLast u (σ h (l ++ [⟨c, .asked r outputs s⟩])).plays (limiterLast σ u h l r)
          outputs := by
  unfold limiterLast
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [limiterStep]
  rw [foldl_limiterStep_fst, List.nil_append, Function.update_self]

/-- An event that is not a request of speaker `r` leaves what the limiter
remembers for `r`. -/
theorem limiterLast_concat_of_ne (σ : Solution H R Msg) (u : ℝ) (h : H)
    (l : List (Event H R Msg)) (e : Event H R Msg) (r : Fin R)
    (hne : ∀ outputs s, e.observation ≠ .asked r outputs s) :
    limiterLast σ u h (l ++ [e]) r = limiterLast σ u h l r := by
  unfold limiterLast
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [limiterStep]
  cases hobs : e.observation with
  | asked r' outputs s =>
    have hr : r ≠ r' := by
      rintro rfl
      exact hne outputs s hobs
    simp only [Function.update_of_ne hr]
  | handed frames stamp => rfl
  | received j c F _ => rfl
  | timer => rfl

/-- Events none of which is a request of speaker `r` leave what the limiter
remembers for `r`. -/
theorem limiterLast_append_of_ne (σ : Solution H R Msg) (u : ℝ) (h : H)
    (l : List (Event H R Msg)) (r : Fin R) :
    ∀ l' : List (Event H R Msg), (∀ e ∈ l', ∀ outputs s, e.observation ≠ .asked r outputs s) →
      limiterLast σ u h (l ++ l') r = limiterLast σ u h l r := by
  intro l'
  induction l' using List.reverseRecOn with
  | nil => intro _; rw [List.append_nil]
  | append_singleton l' e ih =>
    intro hne
    rw [← List.append_assoc, limiterLast_concat_of_ne σ u h (l ++ l') e r
      (hne e (by simp))]
    exact ih fun e' he' => hne e' (List.mem_append_left _ he')

/-! ## The limited solution -/

/-- The solution `σ` with the limiter: the same messages and timers, and at
each request of a playback device the positions that `σ` chooses, passed
through the limiter. -/
def Solution.limited (σ : Solution H R Msg) (u : ℝ) : Solution H R Msg := fun h view =>
  { sends := (σ h view).sends
    timers := (σ h view).timers
    plays :=
      match view.getLast? with
      | some e =>
          match e.observation with
          | .asked r outputs _ =>
              limitAt u (σ h view).plays (limiterLast σ u h view.dropLast r) outputs
          | _ => (σ h view).plays
      | none => (σ h view).plays }

/-- What the limited solution chooses at a request of a playback device. -/
theorem Solution.limited_plays_asked (σ : Solution H R Msg) (u : ℝ) (h : H)
    (l : List (Event H R Msg)) (c : ℝ) (r : Fin R) (outputs : List ℕ) (s : ℝ) :
    ((σ.limited u) h (l ++ [⟨c, .asked r outputs s⟩])).plays
      = limitAt u (σ h (l ++ [⟨c, .asked r outputs s⟩])).plays (limiterLast σ u h l r)
          outputs := by
  simp [Solution.limited]

/-! ## The run of the limited solution -/

section Run

variable [DecidableEq H] (σ : Solution H R Msg) (u : ℝ) (w : World H R) (lookahead : ℕ+)

/-- The event that the host of speaker `r` observes when the playback device
requests block `b`. -/
def World.askedEvent (w : World H R) (r : Fin R) (b : ℕ) : Event H R Msg :=
  ⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
    .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩

/-- What the solution chooses for output sample `k` at step `n` of its run,
when that step handles the request of block `b` of speaker `r`: the position
before the resampler checks that the frames are held. -/
def Solution.chosenAt (n : ℕ) (r : Fin R) (b k : ℕ) : Option ℝ :=
  (σ (w.host r) ((σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r b])).plays k

/-- The step that handles a request of a playback device is unique. -/
theorem Solution.asked_step_unique {n n' : ℕ} {r : Fin R} {b : ℕ}
    (hn : (σ.states w lookahead n).askedNext r = b)
    (he : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r b))
    (hn' : (σ.states w lookahead n').askedNext r = b)
    (he' : earliest ((σ.states w lookahead n').key w) (σ.states w lookahead n').due
      = some (.asked r b)) : n = n' := by
  have hsucc : ∀ {i : ℕ}, (σ.states w lookahead i).askedNext r = b →
      earliest ((σ.states w lookahead i).key w) (σ.states w lookahead i).due
        = some (.asked r b) → ∀ j, i < j → b < (σ.states w lookahead j).askedNext r := by
    intro i hi hei j hij
    have h1 := σ.askedNext_succ w lookahead (n := i) (r := r) (by rw [hi]; exact hei)
    have h2 := Solution.askedNext_mono w σ lookahead r (show i + 1 ≤ j from hij)
    simp only at h2
    omega
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · have := hsucc hn he n' hlt
    omega
  · exact heq
  · have := hsucc hn' he' n hgt
    omega

/-- **What the limiter remembers at the next request.** Let step `n₁` of the
run of `σ` handle the request of block `b` of speaker `r`, and let the
speaker's next request at a later step `n₂` be that of block `b + 1`. Then
at step `n₂` the limiter of any solution `τ`, run over the view of the
speaker's host, remembers the value that it gave the last output sample of
block `b`. -/
theorem Solution.limiterLast_at_next (τ : Solution H R Msg) {n₁ n₂ : ℕ} {r : Fin R} {b : ℕ}
    (hb₁ : (σ.states w lookahead n₁).askedNext r = b)
    (he₁ : earliest ((σ.states w lookahead n₁).key w) (σ.states w lookahead n₁).due
      = some (.asked r b))
    (hlt : n₁ < n₂) (hb₂ : (σ.states w lookahead n₂).askedNext r = b + 1) :
    limiterLast τ u (w.host r) ((σ.states w lookahead n₂).views (w.host r)) r
      = limitLast u
          (τ (w.host r) ((σ.states w lookahead n₁).views (w.host r) ++ [w.askedEvent r b])).plays
          (limiterLast τ u (w.host r) ((σ.states w lookahead n₁).views (w.host r)) r)
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
  rw [hl', hview₁, limiterLast_append_of_ne τ u (w.host r) _ r l' hne]
  exact limiterLast_concat_asked τ u (w.host r) _ _ r _ _

/-- The limited solution and the solution have the same views. -/
theorem Solution.limited_views (n : ℕ) :
    ((σ.limited u).states w lookahead n).views = (σ.states w lookahead n).views :=
  Solution.views_eq_of_sends_eq w lookahead (σ := σ.limited u) (σ' := σ) (fun _ _ => rfl)
    (fun _ _ => rfl) n

/-- The limited solution and the solution handle the requests of the
playback devices at the same steps. -/
theorem Solution.limited_asked_iff (n : ℕ) (r : Fin R) (b : ℕ) :
    (((σ.limited u).states w lookahead n).askedNext r = b
      ∧ earliest (((σ.limited u).states w lookahead n).key w)
          ((σ.limited u).states w lookahead n).due = some (.asked r b))
    ↔ ((σ.states w lookahead n).askedNext r = b
      ∧ earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
          = some (.asked r b)) := by
  have h1 := Solution.askedNext_eq_of_sends_eq w lookahead (σ := σ.limited u) (σ' := σ)
    (fun _ _ => rfl) (fun _ _ => rfl) n
  have h2 := (Solution.earliest_eq_of_sends_eq w lookahead (σ := σ.limited u) (σ' := σ)
    (fun _ _ => rfl) (fun _ _ => rfl) n).2
  rw [h1, h2]

/-- **What the limited solution chooses at a request**: the positions that
the solution chooses there, passed through the limiter, which starts from
the value that it remembers for the speaker. -/
theorem Solution.limited_chosenAt (n : ℕ) (r : Fin R) (b k : ℕ) :
    (σ.limited u).chosenAt w lookahead n r b k
      = limitAt u (σ.chosenAt w lookahead n r b)
          (limiterLast σ u (w.host r) ((σ.states w lookahead n).views (w.host r)) r)
          ((w.speaker r).block b) k := by
  unfold Solution.chosenAt
  rw [σ.limited_views u w lookahead n]
  unfold World.askedEvent
  rw [Solution.limited_plays_asked]

/-- **The limiter runs on from one output sample to the next**, within a
block and from the last output sample of a block to the first of the next.
Let step `n₁` of the run of `σ` handle the request of the block that holds
output sample `k` of speaker `r`, and step `n₂` that of the block that holds
`k + 1`. What the limited solution chooses for `k + 1` is the limiter's step
from what it chooses for `k` and what `σ` chooses for `k + 1`. -/
theorem Solution.limited_chosenAt_succ {n₁ n₂ b₁ b₂ k : ℕ} {r : Fin R}
    (hb₁ : (σ.states w lookahead n₁).askedNext r = b₁)
    (he₁ : earliest ((σ.states w lookahead n₁).key w) (σ.states w lookahead n₁).due
      = some (.asked r b₁))
    (hk₁ : k ∈ (w.speaker r).block b₁)
    (hb₂ : (σ.states w lookahead n₂).askedNext r = b₂)
    (he₂ : earliest ((σ.states w lookahead n₂).key w) (σ.states w lookahead n₂).due
      = some (.asked r b₂))
    (hk₂ : k + 1 ∈ (w.speaker r).block b₂) :
    (σ.limited u).chosenAt w lookahead n₂ r b₂ (k + 1)
      = limitStep u ((σ.limited u).chosenAt w lookahead n₁ r b₁ k)
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
  rw [σ.limited_chosenAt u w lookahead n₂ r b₂ (k + 1),
    σ.limited_chosenAt u w lookahead n₁ r b₁ k]
  by_cases hbb : b₁ = b₂
  · subst hbb
    obtain rfl := σ.asked_step_unique w lookahead hb₁ he₁ hb₂ he₂
    unfold PlaybackDevice.block
    exact limitAt_range'_succ u _ _ _ _ k hr₁.1 (by omega)
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
    rw [σ.limiterLast_at_next u w lookahead σ hb₁ he₁ hn hb₂]
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
    rw [hc₁, hc₂, limitLast_range', hk, hfirst, limitAt_range'_first]
    rfl

/-- **The limited solution keeps the speed bound**, in every world: in every
step of continuous playback its position advances by one frame per output
sample within `u`. -/
theorem Solution.limited_withinStep : (σ.limited u).WithinStep w lookahead u := by
  intro r k x y hx hy hxy hyx
  obtain ⟨b₁, n₁, hk₁, hb₁, he₁, hc₁⟩ :=
    exists_asked_of_plays_some (σ.limited u) w lookahead hx
  obtain ⟨b₂, n₂, hk₂, hb₂, he₂, hc₂⟩ :=
    exists_asked_of_plays_some (σ.limited u) w lookahead hy
  obtain ⟨hb₁', he₁'⟩ := (σ.limited_asked_iff u w lookahead n₁ r b₁).mp ⟨hb₁, he₁⟩
  obtain ⟨hb₂', he₂'⟩ := (σ.limited_asked_iff u w lookahead n₂ r b₂).mp ⟨hb₂, he₂⟩
  have hchain := σ.limited_chosenAt_succ u w lookahead hb₁' he₁' hk₁ hb₂' he₂' hk₂
  have h1 : (σ.limited u).chosenAt w lookahead n₁ r b₁ k = some x := hc₁
  have h2 : (σ.limited u).chosenAt w lookahead n₂ r b₂ (k + 1) = some y := hc₂
  rw [h1, h2] at hchain
  exact limitStep_within hchain.symm hxy hyx

/-- **The limited solution plays what the solution plays, or nothing.** -/
theorem Solution.limited_plays_eq_some {r : Fin R} {k : ℕ} {x : ℝ}
    (h : (σ.limited u).plays w lookahead r k = some x) : σ.plays w lookahead r k = some x := by
  obtain ⟨b, n, hk, hb, he, hc⟩ := exists_asked_of_plays_some (σ.limited u) w lookahead h
  obtain ⟨hb', he'⟩ := (σ.limited_asked_iff u w lookahead n r b).mp ⟨hb, he⟩
  have hc' : (σ.limited u).chosenAt w lookahead n r b k = some x := hc
  rw [σ.limited_chosenAt u w lookahead n r b k] at hc'
  have hσ : σ.chosenAt w lookahead n r b k = some x := limitAt_eq_some hc'
  have hp := (σ.limited u).plays_of_asked_step w lookahead hb he hk
  have hheld := Solution.held_eq_of_sends_eq w lookahead (σ := σ.limited u) (σ' := σ)
    (fun _ _ => rfl) (fun _ _ => rfl) n
  rw [h, hc, hheld] at hp
  have hq := σ.plays_of_asked_step w lookahead hb' he' hk
  have hσ' : (σ (w.host r) ((σ.states w lookahead n).views (w.host r)
      ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
        .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩])).plays k = some x := hσ
  rw [hσ'] at hq
  rw [hq]
  exact hp.symm

/-- **Where the solution's positions are on a line within the bound, the
limiter lets them through.** Suppose that from output sample `K` on, every
position that `σ` chooses for speaker `r` is `a + c * k` at output sample
`k`, with `c` within `u` of one. Then from output sample `K + 1` on the
limited solution plays what `σ` plays. -/
theorem Solution.limited_plays_eq {r : Fin R} {K : ℕ} {a c : ℝ} (hc : |c - 1| ≤ u)
    (hline : ∀ n b k, K ≤ k → k ∈ (w.speaker r).block b →
      (σ.states w lookahead n).askedNext r = b →
      earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
        = some (.asked r b) →
      ∀ x, σ.chosenAt w lookahead n r b k = some x → x = a + c * k) :
    ∀ k, K + 1 ≤ k → (σ.limited u).plays w lookahead r k = σ.plays w lookahead r k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : K ≤ j := by omega
  -- A request step of the block of `j + 1`, if either solution plays there.
  have hmain : ∀ (b₂ n₂ : ℕ), j + 1 ∈ (w.speaker r).block b₂ →
      (σ.states w lookahead n₂).askedNext r = b₂ →
      earliest ((σ.states w lookahead n₂).key w) (σ.states w lookahead n₂).due
        = some (.asked r b₂) →
      (σ.limited u).plays w lookahead r (j + 1) = σ.plays w lookahead r (j + 1) := by
    intro b₂ n₂ hk₂ hb₂ he₂
    have hmono := (w.speaker r).first_strictMono
    have hr₂ : (w.speaker r).first b₂ ≤ j + 1 ∧ j + 1 < (w.speaker r).first (b₂ + 1) := by
      have h := hk₂
      unfold PlaybackDevice.block at h
      rw [List.mem_range'_1] at h
      have := hmono (Nat.lt_add_one b₂)
      omega
    -- A request step of the block of `j`.
    obtain ⟨b₁, n₁, hk₁, hb₁, he₁⟩ : ∃ b₁ n₁, j ∈ (w.speaker r).block b₁
        ∧ (σ.states w lookahead n₁).askedNext r = b₁
        ∧ earliest ((σ.states w lookahead n₁).key w) (σ.states w lookahead n₁).due
          = some (.asked r b₁) := by
      by_cases hin : (w.speaker r).first b₂ ≤ j
      · refine ⟨b₂, n₂, ?_, hb₂, he₂⟩
        unfold PlaybackDevice.block
        rw [List.mem_range'_1]
        omega
      · have hb0 : b₂ ≠ 0 := by
          rintro rfl
          have := (w.speaker r).first_zero
          omega
        obtain ⟨b₁, rfl⟩ : ∃ b₁, b₂ = b₁ + 1 := ⟨b₂ - 1, by omega⟩
        obtain ⟨n₁, -, hb₁, he₁⟩ := σ.exists_asked_step w lookahead (m := n₂) (r := r) (b := b₁)
          (by rw [hb₂]; exact Nat.lt_succ_self b₁)
        refine ⟨b₁, n₁, ?_, hb₁, he₁⟩
        unfold PlaybackDevice.block
        rw [List.mem_range'_1]
        have := hmono (Nat.lt_add_one b₁)
        omega
    have hchain := σ.limited_chosenAt_succ u w lookahead hb₁ he₁ hk₁ hb₂ he₂ hk₂
    -- What the limiter gave output sample `j` is nothing, or on the line.
    have hprev : ∀ x, (σ.limited u).chosenAt w lookahead n₁ r b₁ j = some x → x = a + c * j := by
      intro x hx
      rw [σ.limited_chosenAt u w lookahead n₁ r b₁ j] at hx
      exact hline n₁ b₁ j hj hk₁ hb₁ he₁ x (limitAt_eq_some hx)
    have hsame : (σ.limited u).chosenAt w lookahead n₂ r b₂ (j + 1)
        = σ.chosenAt w lookahead n₂ r b₂ (j + 1) := by
      rw [hchain]
      cases hy : σ.chosenAt w lookahead n₂ r b₂ (j + 1) with
      | none => exact limitStep_none_right u _
      | some y =>
        have hyl := hline n₂ b₂ (j + 1) (Nat.le_succ_of_le hj) hk₂ hb₂ he₂ y hy
        cases hx : (σ.limited u).chosenAt w lookahead n₁ r b₁ j with
        | none => exact limitStep_none_left u _
        | some x =>
          have hxl := hprev x hx
          refine limitStep_of_within fun _ _ => ?_
          have e : y - x - 1 = c - 1 := by
            rw [hxl, hyl]
            push_cast
            ring
          rw [e]
          exact hc
    obtain ⟨hb₂', he₂'⟩ := (σ.limited_asked_iff u w lookahead n₂ r b₂).mpr ⟨hb₂, he₂⟩
    have hp := (σ.limited u).plays_of_asked_step w lookahead hb₂' he₂' hk₂
    have hq := σ.plays_of_asked_step w lookahead hb₂ he₂ hk₂
    have hheld := Solution.held_eq_of_sends_eq w lookahead (σ := σ.limited u) (σ' := σ)
      (fun _ _ => rfl) (fun _ _ => rfl) n₂
    have hsame' : ((σ.limited u) (w.host r) (((σ.limited u).states w lookahead n₂).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b₂),
          .asked r ((w.speaker r).block b₂) ((w.speaker r).reported b₂)⟩])).plays (j + 1)
        = (σ (w.host r) ((σ.states w lookahead n₂).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b₂),
          .asked r ((w.speaker r).block b₂) ((w.speaker r).reported b₂)⟩])).plays (j + 1) := hsame
    rw [hp, hq, hheld, hsame']
  cases hl : (σ.limited u).plays w lookahead r (j + 1) with
  | some x =>
    obtain ⟨b, n, hkb, hb, he, -⟩ := exists_asked_of_plays_some (σ.limited u) w lookahead hl
    obtain ⟨hb', he'⟩ := (σ.limited_asked_iff u w lookahead n r b).mp ⟨hb, he⟩
    rw [← hl]
    exact hmain b n hkb hb' he'
  | none =>
    cases hs : σ.plays w lookahead r (j + 1) with
    | none => rfl
    | some x =>
      obtain ⟨b, n, hkb, hb, he, -⟩ := exists_asked_of_plays_some σ w lookahead hs
      rw [← hl, ← hs]
      exact hmain b n hkb hb he

end Run

end Unisono.Spec
