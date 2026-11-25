/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Held

/-!
# What a run does before a time does not depend on later deliveries

Take two worlds with the same hosts, clocks, audio devices and target
latencies, whose networks differ only in when they deliver messages, and
only in deliveries that arrive at or after a true time `T` in both worlds.
This file proves that every solution plays the same, in both worlds, at
every output sample of every playback block that is requested before `T`.

* `State.SameBefore`: two states of a run agree up to `T`: they are equal
  except that a message in transit may arrive at different times in the two,
  both at or after `T`.
* `State.SameBefore.step`: when the earliest pending event of the first
  state occurs before `T`, it is the earliest pending event of the second
  state too, and the two states after it agree up to `T` again.
* `Solution.sameBefore_states`: so the states of the two runs agree up to
  `T` at every step before which every event occurred before `T`.
* `Solution.plays_eq_of_sameBefore`: what a speaker plays at the output
  samples of a playback block requested before `T` is the same in both
  worlds.

The statement is about any solution and any two such worlds. It is the form
of causality that a lower bound for random pauses needs: a pause that begins
at a true time changes only deliveries that arrive after that time.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

/-! ## The earliest element under two keys -/

/-- If two keys agree on every element of a list except on elements whose
time is at or after `T` under both, and the earliest element under the first
key has a time before `T`, then it is the earliest element under the second
key too. -/
theorem earliest_eq_of_agree {α : Type} (key₁ key₂ : α → Time × ℕ) {T : Time} :
    ∀ (l : List α) (a : α), earliest key₁ l = some a → (key₁ a).1 < T →
      (∀ b ∈ l, key₂ b = key₁ b ∨ (T ≤ (key₁ b).1 ∧ T ≤ (key₂ b).1)) →
      earliest key₂ l = some a
  | [], a, h, _, _ => by simp [earliest] at h
  | c :: l, a, h, hT, hag => by
      simp only [earliest] at h ⊢
      have hagl : ∀ x ∈ l, key₂ x = key₁ x ∨ (T ≤ (key₁ x).1 ∧ T ≤ (key₂ x).1) :=
        fun x hx => hag x (List.mem_cons_of_mem _ hx)
      cases hl : earliest key₁ l with
      | none =>
        simp only [hl, Option.some.injEq] at h
        subst h
        cases l with
        | nil => simp [earliest]
        | cons d l' => exact absurd hl (earliest_ne_none key₁ d l')
      | some b =>
        simp only [hl] at h
        obtain ⟨hb, hmin⟩ := earliest_spec_lex key₁ l b hl
        split_ifs at h with hc
        · -- The head is selected.
          simp only [Option.some.injEq] at h
          subst h
          have hc₂ : key₂ c = key₁ c := by
            rcases hag c (List.mem_cons_self ..) with h1 | ⟨h1, -⟩
            · exact h1
            · exact absurd hT (not_lt.mpr h1)
          cases hl₂ : earliest key₂ l with
          | none => rfl
          | some b' =>
            obtain ⟨hb', -⟩ := earliest_spec_lex key₂ l b' hl₂
            have hbb' := hmin b' hb'
            dsimp only
            rw [ite_eq_left]
            rw [hc₂]
            rcases hagl b' hb' with h2 | ⟨-, h2⟩
            · rw [h2]
              rcases hc with hc | ⟨hc1, hc2⟩ <;> rcases hbb' with hbb | ⟨hbb1, hbb2⟩
              · exact Or.inl (hc.trans hbb)
              · exact Or.inl (hbb1 ▸ hc)
              · exact Or.inl (hc1 ▸ hbb)
              · exact Or.inr ⟨hc1.trans hbb1, hc2.trans hbb2⟩
            · exact Or.inl (lt_of_lt_of_le hT h2)
        · -- The earliest element of the tail is selected.
          simp only [Option.some.injEq] at h
          subst h
          have ih := earliest_eq_of_agree key₁ key₂ l b hl hT hagl
          have hb₂ : key₂ b = key₁ b := by
            rcases hagl b hb with h1 | ⟨h1, -⟩
            · exact h1
            · exact absurd hT (not_lt.mpr h1)
          rw [ih]
          dsimp only
          rw [ite_eq_right]
          rw [hb₂]
          rcases hag c (List.mem_cons_self ..) with h1 | ⟨-, h1⟩
          · rw [h1]
            exact hc
          · rintro (h2 | ⟨h2, -⟩)
            · exact absurd (h2.trans hT) (not_lt.mpr h1)
            · rw [h2] at h1
              exact absurd hT (not_lt.mpr h1)

/-! ## Lists that are related element by element -/

/-- Two lists related element by element have related elements at each
index, or none at that index. -/
theorem forall₂_getElem? {α β : Type} {S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ S l₁ l₂ → ∀ p : ℕ,
      (l₁[p]? = none ∧ l₂[p]? = none) ∨ ∃ a b, l₁[p]? = some a ∧ l₂[p]? = some b ∧ S a b
  | _, _, .nil, _ => Or.inl ⟨rfl, rfl⟩
  | _, _, .cons h _, 0 => Or.inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ t, p + 1 => by simpa using forall₂_getElem? t p

/-- Two lists related element by element stay so when the element at one
index is removed from both. -/
theorem forall₂_eraseIdx {α β : Type} {S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ S l₁ l₂ → ∀ p : ℕ,
      List.Forall₂ S (l₁.eraseIdx p) (l₂.eraseIdx p)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ t, 0 => by simpa using t
  | _, _, .cons h t, p + 1 => by simpa using List.Forall₂.cons h (forall₂_eraseIdx t p)

/-! ## States that agree up to a time -/

/-- Two messages in transit are the same up to `T`: they have the same
origin, destination, payload and frames, and they arrive at the same time or
both at or after `T`. -/
def InFlight.SameBefore (T : Time) (m₁ m₂ : InFlight H Msg) : Prop :=
  m₁.origin = m₂.origin ∧ m₁.destination = m₂.destination ∧ m₁.contents = m₂.contents
    ∧ m₁.frames = m₂.frames ∧ (m₁.arrival = m₂.arrival ∨ (T ≤ m₁.arrival ∧ T ≤ m₂.arrival))

theorem InFlight.SameBefore.refl (T : Time) (m : InFlight H Msg) : InFlight.SameBefore T m m :=
  ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- Two messages that are the same up to `T`, one of which arrives before
`T`, are equal. -/
theorem InFlight.SameBefore.eq_of_lt {T : Time} {m₁ m₂ : InFlight H Msg}
    (h : InFlight.SameBefore T m₁ m₂) (hlt : m₁.arrival < T) : m₁ = m₂ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have harr : m₁.arrival = m₂.arrival := by
    rcases h5 with h5 | ⟨h5, -⟩
    · exact h5
    · exact absurd hlt (not_lt.mpr h5)
  cases m₁
  cases m₂
  dsimp only at harr h1 h2 h3 h4
  rw [InFlight.mk.injEq]
  exact ⟨harr, h1, h2, h3, h4⟩

/-- Two states of a run agree up to `T`: they are equal except that a
message in transit may arrive at different times in the two, both at or
after `T`. -/
structure State.SameBefore (T : Time) (st₁ st₂ : State H R Msg) : Prop where
  views : st₁.views = st₂.views
  handedNext : st₁.handedNext = st₂.handedNext
  askedNext : st₁.askedNext = st₂.askedNext
  inFlight : List.Forall₂ (InFlight.SameBefore T) st₁.inFlight st₂.inFlight
  timers : st₁.timers = st₂.timers
  sentCount : st₁.sentCount = st₂.sentCount
  held : st₁.held = st₂.held
  plays : st₁.plays = st₂.plays
  sent : st₁.sent = st₂.sent

theorem State.SameBefore.due_eq {T : Time} {st₁ st₂ : State H R Msg}
    (h : st₁.SameBefore T st₂) : st₁.due = st₂.due := by
  unfold State.due
  rw [h.handedNext, h.askedNext, h.inFlight.length_eq, h.timers]

variable [DecidableEq H]

/-- The two worlds deliver each message at the same time, or both at or
after `T`. -/
def World.DeliversSameBefore (T : Time) (w₁ w₂ : World H R) : Prop :=
  ∀ i j t q, w₁.network.deliver i j t q = w₂.network.deliver i j t q ∨
    ∃ a₁ a₂, w₁.network.deliver i j t q = some a₁ ∧ w₂.network.deliver i j t q = some a₂
      ∧ T ≤ a₁ ∧ T ≤ a₂

theorem State.SameBefore.send {T : Time} {w₁ w₂ : World H R}
    (hnet : World.DeliversSameBefore T w₁ w₂) {st₁ st₂ : State H R Msg}
    (h : st₁.SameBefore T st₂) (i : H) (t : Time) (j : H) (c : Msg) (F : Finset ℕ) :
    (st₁.send w₁ i t j c F).SameBefore T (st₂.send w₂ i t j c F) := by
  have hcount : st₂.sentCount i j = st₁.sentCount i j := by rw [h.sentCount]
  refine ⟨h.views, h.handedNext, h.askedNext, ?_, h.timers, ?_, h.held, h.plays, ?_⟩
  · simp only [State.send]
    rw [hcount]
    rcases hnet i j t (st₁.sentCount i j) with heq | ⟨a₁, a₂, h1, h2, hT1, hT2⟩
    · rw [← heq]
      cases w₁.network.deliver i j t (st₁.sentCount i j) with
      | none => exact h.inFlight
      | some a =>
        exact List.rel_append h.inFlight
          (List.Forall₂.cons (InFlight.SameBefore.refl T _) List.Forall₂.nil)
    · rw [h1, h2]
      exact List.rel_append h.inFlight
        (List.Forall₂.cons ⟨rfl, rfl, rfl, rfl, Or.inr ⟨hT1, hT2⟩⟩ List.Forall₂.nil)
  · simp only [State.send]
    rw [h.sentCount]
  · simp only [State.send]
    rw [h.sent]

theorem State.SameBefore.sendAll {T : Time} {w₁ w₂ : World H R}
    (hnet : World.DeliversSameBefore T w₁ w₂) (i : H) (t : Time) (held : Finset ℕ) :
    ∀ (sends : List (H × Msg × Finset ℕ)) {st₁ st₂ : State H R Msg}, st₁.SameBefore T st₂ →
      (st₁.sendAll w₁ i t held sends).SameBefore T (st₂.sendAll w₂ i t held sends)
  | [], _, _, h => h
  | s :: rest, _, _, h => by
      simp only [State.sendAll, List.foldl_cons]
      exact State.SameBefore.sendAll hnet i t held rest (h.send hnet i t s.1 s.2.1 _)

theorem State.SameBefore.handle {T : Time} {w₁ w₂ : World H R} (hclock : w₂.clock = w₁.clock)
    (hspk : w₂.speaker = w₁.speaker)
    (hnet : World.DeliversSameBefore T w₁ w₂) (σ : Solution H R Msg) (lookahead : ℕ+)
    {st₁ st₂ : State H R Msg} (h : st₁.SameBefore T st₂) (i : H) (t : Time)
    (obs : Observation H R Msg) :
    (st₁.handle σ w₁ lookahead i t obs).SameBefore T (st₂.handle σ w₂ lookahead i t obs) := by
  have hbase : ({ st₁ with
        views := Function.update st₁.views i (st₁.views i ++ [⟨(w₁.clock i).read t, obs⟩])
        held := Function.update st₁.held i (st₁.held i ∪ obs.frames) } :
        State H R Msg).SameBefore T
      ({ st₂ with
        views := Function.update st₂.views i (st₁.views i ++ [⟨(w₁.clock i).read t, obs⟩])
        held := Function.update st₂.held i (st₁.held i ∪ obs.frames) } : State H R Msg) :=
    ⟨by simp only [h.views], h.handedNext, h.askedNext, h.inFlight, h.timers, h.sentCount,
      by simp only [h.held], h.plays, h.sent⟩
  have hsends := State.SameBefore.sendAll hnet i t (st₁.held i ∪ obs.frames)
    (σ i (st₁.views i ++ [⟨(w₁.clock i).read t, obs⟩])).sends hbase
  have hv : st₂.views i = st₁.views i := by rw [h.views]
  have hh : st₂.held i = st₁.held i := by rw [h.held]
  dsimp only [State.handle]
  rw [hclock, hv, hh, hspk]
  refine ⟨hsends.views, hsends.handedNext, hsends.askedNext, hsends.inFlight, ?_,
    hsends.sentCount, hsends.held, ?_, hsends.sent⟩
  · simp only [hsends.timers]
  · cases obs <;> simp only [hsends.plays]

theorem State.SameBefore.key {T : Time} {w₁ w₂ : World H R} (hsender : w₂.sender = w₁.sender)
    (hhost : w₂.host = w₁.host) (hsrc : w₂.source = w₁.source)
    (hspk : w₂.speaker = w₁.speaker) {st₁ st₂ : State H R Msg} (h : st₁.SameBefore T st₂)
    (e : Due R) :
    st₂.key w₂ e = st₁.key w₁ e ∨ (T ≤ (st₁.key w₁ e).1 ∧ T ≤ (st₂.key w₂ e).1) := by
  have hidx : w₂.hostIndex = w₁.hostIndex := by
    funext x
    unfold World.hostIndex
    rw [hsender, hhost]
  cases e with
  | handed b =>
    left
    simp [State.key, hsrc]
  | asked r b =>
    left
    simp [State.key, hspk]
  | arrival p =>
    rcases forall₂_getElem? h.inFlight p with ⟨h1, h2⟩ | ⟨m₁, m₂, h1, h2, hm⟩
    · left
      simp [State.key, h1, h2]
    · obtain ⟨ho, -, -, -, harr⟩ := hm
      rcases harr with harr | ⟨hT1, hT2⟩
      · left
        simp [State.key, h1, h2, harr, ho, hidx]
      · right
        simp [State.key, h1, h2, hT1, hT2]
  | timer p =>
    left
    simp [State.key, h.timers]

/-- **One step keeps two states in agreement up to `T`.** Consider two
worlds with the same hosts, clocks, audio devices and target latencies that
deliver each message at the same time or both at or after `T`, and two
states that agree up to `T`. If the earliest pending event of the first
state occurs before `T`, it is the earliest pending event of the second
state too, and the states after the step agree up to `T`. -/
theorem State.SameBefore.step {T : Time} {w₁ w₂ : World H R} (hsender : w₂.sender = w₁.sender)
    (hhost : w₂.host = w₁.host) (hclock : w₂.clock = w₁.clock) (hsrc : w₂.source = w₁.source)
    (hspk : w₂.speaker = w₁.speaker) (htgt : w₂.target = w₁.target)
    (hnet : World.DeliversSameBefore T w₁ w₂) (σ : Solution H R Msg) (lookahead : ℕ+)
    {st₁ st₂ : State H R Msg} (h : st₁.SameBefore T st₂) {e : Due R}
    (he : earliest (st₁.key w₁) st₁.due = some e) (hT : (st₁.key w₁ e).1 < T) :
    earliest (st₂.key w₂) st₂.due = some e
      ∧ (st₁.step σ w₁ lookahead).SameBefore T (st₂.step σ w₂ lookahead) := by
  have he₂ : earliest (st₂.key w₂) st₂.due = some e := by
    rw [← h.due_eq]
    exact earliest_eq_of_agree _ _ _ _ he hT fun b _ => h.key hsender hhost hsrc hspk b
  refine ⟨he₂, ?_⟩
  unfold State.step
  rw [he, he₂]
  cases e with
  | handed b =>
    dsimp only
    rw [hsender, hsrc, htgt]
    have hh := h.handle hclock hspk hnet σ lookahead w₁.sender (w₁.source.handed b)
      (.handed ((w₁.source.block b).map fun n => (n, w₁.target n)) (w₁.source.reported b))
    exact ⟨hh.views, rfl, hh.askedNext, hh.inFlight, hh.timers, hh.sentCount, hh.held,
      hh.plays, hh.sent⟩
  | asked r b =>
    dsimp only
    rw [hhost, hspk]
    have hh := h.handle hclock hspk hnet σ lookahead (w₁.host r) ((w₁.speaker r).asked b)
      (.asked r ((w₁.speaker r).block b) ((w₁.speaker r).reported b))
    exact ⟨hh.views, hh.handedNext, by simp only [h.askedNext], hh.inFlight, hh.timers,
      hh.sentCount, hh.held, hh.plays, hh.sent⟩
  | arrival p =>
    dsimp only
    rcases forall₂_getElem? h.inFlight p with ⟨h1, h2⟩ | ⟨m₁, m₂, h1, h2, hm⟩
    · rw [h1, h2]
      exact h
    · have hkey : (st₁.key w₁ (.arrival p)).1 = m₁.arrival := by simp [State.key, h1]
      rw [hkey] at hT
      have hmm := hm.eq_of_lt hT
      subst hmm
      rw [h1, h2]
      dsimp only
      have hrel : State.SameBefore T
          ({ st₁ with inFlight := st₁.inFlight.eraseIdx p } : State H R Msg)
          { st₂ with inFlight := st₂.inFlight.eraseIdx p } :=
        ⟨h.views, h.handedNext, h.askedNext, forall₂_eraseIdx h.inFlight p, h.timers,
          h.sentCount, h.held, h.plays, h.sent⟩
      exact hrel.handle hclock hspk hnet σ lookahead _ _ _
  | timer p =>
    dsimp only
    rw [← h.timers]
    cases hu : st₁.timers[p]? with
    | none => exact h
    | some u =>
      dsimp only
      have hrel : State.SameBefore T
          ({ st₁ with timers := st₁.timers.eraseIdx p } : State H R Msg)
          { st₂ with timers := st₁.timers.eraseIdx p } :=
        ⟨h.views, h.handedNext, h.askedNext, h.inFlight, rfl, h.sentCount, h.held, h.plays,
          h.sent⟩
      exact hrel.handle hclock hspk hnet σ lookahead _ _ _

/-- **The two runs agree up to `T` while their events occur before `T`.**
Consider two worlds with the same hosts, clocks, audio devices and target
latencies that deliver each message at the same time or both at or after
`T`. At every step `n` such that every earlier step of the run in the first
world handled an event before `T`, the states of the two runs agree up to
`T`. -/
theorem Solution.sameBefore_states (σ : Solution H R Msg) {T : Time} {w₁ w₂ : World H R}
    (hsender : w₂.sender = w₁.sender) (hhost : w₂.host = w₁.host)
    (hclock : w₂.clock = w₁.clock) (hsrc : w₂.source = w₁.source)
    (hspk : w₂.speaker = w₁.speaker) (htgt : w₂.target = w₁.target)
    (hnet : World.DeliversSameBefore T w₁ w₂) (lookahead : ℕ+) :
    ∀ n, (∀ j < n, σ.eventTime w₁ lookahead j < T) →
      (σ.states w₁ lookahead n).SameBefore T (σ.states w₂ lookahead n)
  | 0, _ => ⟨rfl, rfl, rfl, List.Forall₂.nil, rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hT => by
      have ih := Solution.sameBefore_states σ hsender hhost hclock hsrc hspk htgt hnet
        lookahead n fun j hj => hT j (Nat.lt_succ_of_lt hj)
      obtain ⟨e, he⟩ := earliest_exists ((σ.states w₁ lookahead n).key w₁)
        (σ.states w₁ lookahead n).due_ne_nil
      have hTn := hT n (Nat.lt_succ_self n)
      simp only [Solution.eventTime, he] at hTn
      exact (ih.step hsender hhost hclock hsrc hspk htgt hnet σ lookahead he hTn).2

/-- **What a speaker plays before `T` does not depend on later
deliveries.** Consider two worlds with the same hosts, clocks, audio devices
and target latencies that deliver each message at the same time or both at
or after `T`. Every solution plays the same in both at every output sample
of every playback block that is requested before `T`. -/
theorem Solution.plays_eq_of_sameBefore (σ : Solution H R Msg) {T : Time} {w₁ w₂ : World H R}
    (hsender : w₂.sender = w₁.sender) (hhost : w₂.host = w₁.host)
    (hclock : w₂.clock = w₁.clock) (hsrc : w₂.source = w₁.source)
    (hspk : w₂.speaker = w₁.speaker) (htgt : w₂.target = w₁.target)
    (hnet : World.DeliversSameBefore T w₁ w₂) (lookahead : ℕ+) {r : Fin R} {b k : ℕ}
    (hb : (w₁.speaker r).asked b < T) (hk : k ∈ (w₁.speaker r).block b) :
    σ.plays w₂ lookahead r k = σ.plays w₁ lookahead r k := by
  classical
  have hkb : (w₁.speaker r).first b ≤ k ∧ k < (w₁.speaker r).first (b + 1) := by
    unfold PlaybackDevice.block at hk
    rw [List.mem_range'_1] at hk
    have := (w₁.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  -- While the request of block `b` is pending, events occur before `T`.
  have hTime : ∀ n, (σ.states w₁ lookahead n).askedNext r ≤ b →
      σ.eventTime w₁ lookahead n < T := by
    intro n hn
    have h1 := (σ.eventTime_dueFrom w₁ lookahead n).2.1 r
    have h2 : (w₁.speaker r).asked ((σ.states w₁ lookahead n).askedNext r)
        ≤ (w₁.speaker r).asked b := (w₁.speaker r).asked_mono hn
    linarith
  -- A step before which the output sample is not yet decided.
  have hpending : ∀ n, ¬ k < (w₁.speaker r).first ((σ.states w₁ lookahead n).askedNext r) →
      (σ.states w₁ lookahead n).askedNext r ≤ b := by
    intro n hn
    by_contra hlt
    have h1 : b + 1 ≤ (σ.states w₁ lookahead n).askedNext r := by omega
    have h2 := (w₁.speaker r).first_strictMono.monotone h1
    omega
  have hsame : ∀ n, (∀ j < n,
        ¬ k < (w₁.speaker r).first ((σ.states w₁ lookahead j).askedNext r)) →
      (σ.states w₁ lookahead n).SameBefore T (σ.states w₂ lookahead n) := fun n hn =>
    σ.sameBefore_states hsender hhost hclock hsrc hspk htgt hnet lookahead n
      fun j hj => hTime j (hpending j (hn j hj))
  unfold Solution.plays
  rw [hspk]
  by_cases hex : ∃ n, k < (w₁.speaker r).first ((σ.states w₁ lookahead n).askedNext r)
  · have hmin : ∀ j < Nat.find hex,
        ¬ k < (w₁.speaker r).first ((σ.states w₁ lookahead j).askedNext r) :=
      fun j hj => Nat.find_min hex hj
    have hS := hsame (Nat.find hex) hmin
    have hex₂ : ∃ n, k < (w₁.speaker r).first ((σ.states w₂ lookahead n).askedNext r) :=
      ⟨Nat.find hex, by rw [← hS.askedNext]; exact Nat.find_spec hex⟩
    have hfind : Nat.find hex₂ = Nat.find hex := by
      rw [Nat.find_eq_iff]
      refine ⟨by rw [← hS.askedNext]; exact Nat.find_spec hex, fun j hj => ?_⟩
      have hSj := hsame j fun i hi => hmin i (hi.trans hj)
      rw [← hSj.askedNext]
      exact hmin j hj
    rw [dite_eq_left hex₂, dite_eq_left hex, hfind, hS.plays]
  · have hall : ∀ n, ¬ k < (w₁.speaker r).first ((σ.states w₁ lookahead n).askedNext r) :=
      fun n hn => hex ⟨n, hn⟩
    have hex₂ : ¬ ∃ n, k < (w₁.speaker r).first ((σ.states w₂ lookahead n).askedNext r) := by
      rintro ⟨n, hn⟩
      have hS := hsame n fun j _ => hall j
      rw [← hS.askedNext] at hn
      exact hall n hn
    rw [dite_eq_right hex₂, dite_eq_right hex]

end Unisono.Spec
