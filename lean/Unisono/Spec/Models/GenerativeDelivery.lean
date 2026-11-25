/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeWorld

/-!
# When a message arrives in a world with pauses

In a world built from a draw of the generative model
(`GenerativeWorld.Builds`), a message waits for three backlogs: that of the
host that sends it, that of the link, and that of the host that receives it.
This file names the time at which a message arrives as a function of the
draw (`Draw.arrival`) and proves what holds for every draw.

* Every message arrives at that time, whichever message of its link it is
  (`Builds.deliver`). No message is lost.
* A message takes at least the least delay of its direction
  (`Builds.le_arrival`).
* **Messages do not overtake one another.** When the paused time that has
  begun never decreases, a message sent later on the same link arrives no
  earlier (`Builds.arrival_mono`). The reason is that a backlog falls by at
  most one second per second: `t + backlog t` never decreases
  (`IsBacklog.add_le_add`). Messages sent while a link or a host is paused
  arrive together when the pause ends, so equal arrival times are common.

A host handles the events of its audio devices after its backlog as well.

* The host of a speaker handles a request no earlier than the device raises
  it, which is the request lead before the block's first output sample
  leaves (`Builds.exists_request_le_asked`).
* A host that never pauses handles the events of its devices when they
  occur (`Builds.handed_of_const`, `Builds.asked_of_const`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- The backlog at true time `t` of a link or a host whose paused time is
recorded by `paused`: the least upper bound that `IsBacklog` describes, when
there is one. -/
def backlog (paused : Time → ℝ) (t : Time) : ℝ :=
  sSup {x | ∃ s ≤ t, x = paused t - paused s - (t - s)}

/-- A backlog is the value of `backlog`. -/
theorem IsBacklog.backlog_eq {paused : Time → ℝ} {t : Time} {v : ℝ}
    (h : IsBacklog paused t v) : backlog paused t = v :=
  h.csSup_eq ⟨0, t, le_rfl, by simp⟩

/-- A backlog is not negative. -/
theorem IsBacklog.nonneg {paused : Time → ℝ} {t : Time} {v : ℝ} (h : IsBacklog paused t v) :
    0 ≤ v :=
  h.1 ⟨t, le_rfl, by simp⟩

/-- **A backlog falls by at most one second per second.** When the paused
time that has begun never decreases, the true time at which the backlog of
time `t` is worked off, `t + v`, is no later than that of any later time. -/
theorem IsBacklog.add_le_add {paused : Time → ℝ} (hmono : Monotone paused) {t t' : Time}
    {v v' : ℝ} (h : IsBacklog paused t v) (h' : IsBacklog paused t' v') (htt' : t ≤ t') :
    t + v ≤ t' + v' := by
  have hv : v ≤ v' + (t' - t) := by
    apply h.2
    rintro x ⟨s, hs, rfl⟩
    have h1 := h'.1 ⟨s, hs.trans htt', rfl⟩
    have h2 := hmono htt'
    linarith
  linarith

/-- When host `j` observes a message that host `i` sends at true time `s`,
by the draw. The message leaves `i` after the backlog of host `i` at `s`,
reaches `j` after the least delay of the direction plus the backlog of the
link when it leaves, and is observed after the backlog of host `j` when it
reaches it. -/
def Draw.arrival (d : Draw H R) (f : Member H R) (i j : H) (s : Time) : Time :=
  s + backlog (d.hostPaused i) s + d.split i j * f.roundTrip i j
    + backlog (d.linkPaused i j) (s + backlog (d.hostPaused i) s)
    + backlog (d.hostPaused j)
        (s + backlog (d.hostPaused i) s + d.split i j * f.roundTrip i j
          + backlog (d.linkPaused i j) (s + backlog (d.hostPaused i) s))

/-- **Every message arrives when the draw says.** In a world built from a
draw, a message from `i` to `j` sent at true time `s` arrives at
`d.arrival f i j s`, whichever message of the link it is. -/
theorem Builds.deliver (hB : m.Builds f d w) (i j : H) (s : Time) (q : ℕ) :
    w.network.deliver i j s q = some (d.arrival f i j s) := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hd⟩ := hB.network i j s q
  have e₁ := hv₁.backlog_eq
  have e₂ := hv₂.backlog_eq
  have e₃ := hv₃.backlog_eq
  rw [hd]
  unfold Draw.arrival
  rw [e₁, e₂, e₃]

/-- The three backlogs that a message waits for: the backlog `v₁` of the
sending host when the message is sent, the backlog `v₂` of the link when the
message leaves, and the backlog `v₃` of the receiving host when the message
reaches it. -/
theorem Builds.arrival_eq (hB : m.Builds f d w) (i j : H) (s : Time) :
    ∃ v₁ v₂ v₃, IsBacklog (d.hostPaused i) s v₁
      ∧ IsBacklog (d.linkPaused i j) (s + v₁) v₂
      ∧ IsBacklog (d.hostPaused j) (s + v₁ + d.split i j * f.roundTrip i j + v₂) v₃
      ∧ d.arrival f i j s = s + v₁ + d.split i j * f.roundTrip i j + v₂ + v₃ := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hd⟩ := hB.network i j s 0
  refine ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, ?_⟩
  rw [hB.deliver i j s 0] at hd
  exact Option.some.inj hd

/-- **A message takes at least the least delay of its direction.** -/
theorem Builds.le_arrival (hB : m.Builds f d w) (i j : H) (s : Time) :
    s + d.split i j * f.roundTrip i j ≤ d.arrival f i j s := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  have h₁ := hv₁.nonneg
  have h₂ := hv₂.nonneg
  have h₃ := hv₃.nonneg
  linarith

/-- **Messages do not overtake one another.** When the paused time of the
link and of both hosts never decreases, a message sent later from `i` to `j`
arrives no earlier. -/
theorem Builds.arrival_mono (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) (hi : Monotone (d.hostPaused i))
    (hj : Monotone (d.hostPaused j)) : Monotone (d.arrival f i j) := by
  intro s s' hss'
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  obtain ⟨v₁', v₂', v₃', hv₁', hv₂', hv₃', he'⟩ := hB.arrival_eq i j s'
  have h₁ := hv₁.add_le_add hi hv₁' hss'
  have h₂ := hv₂.add_le_add hlink hv₂' h₁
  have h₃ := hv₃.add_le_add hj hv₃' (by linarith)
  rw [he, he']
  linarith

/-- When no paused time begins, the backlog is zero. -/
theorem isBacklog_zero_of_const {paused : Time → ℝ} (hc : ∀ s t, paused s = paused t)
    (t : Time) : IsBacklog paused t 0 := by
  constructor
  · rintro x ⟨s, hs, rfl⟩
    rw [hc t s]
    linarith
  · intro u hu
    exact hu ⟨t, le_rfl, by simp⟩
/-- **A request is handled no earlier than the device raises it.** The
device of speaker `r` raises the request of block `b` at a true time `ρ`
that is the request lead, on the device's clock, before the block's first
output sample leaves; the host handles it at `ρ` or later. -/
theorem Builds.exists_request_le_asked (hB : m.Builds f d w) (r : Fin R) (b : ℕ) :
    ∃ ρ ≤ (w.speaker r).asked b,
      d.deviceReading (some (m.device r)) ((w.speaker r).out ((w.speaker r).first b))
        - d.deviceReading (some (m.device r)) ρ = m.lead := by
  obtain ⟨ρ, v, hρ, hv, h⟩ := hB.speaker_asked r b
  exact ⟨ρ, by rw [h]; linarith [hv.nonneg], hρ⟩

/-- **A sender's host that never pauses handles each handover when the
block's last frame is captured.** -/
theorem Builds.handed_of_const (hB : m.Builds f d w)
    (hc : ∀ s t, d.hostPaused w.sender s = d.hostPaused w.sender t) (b : ℕ) :
    w.source.handed b = w.source.capture (w.source.first (b + 1) - 1) := by
  obtain ⟨v, hv, h⟩ := hB.capture_handed b
  rw [h, hv.unique (isBacklog_zero_of_const hc _), add_zero]

/-- **A speaker's host that never pauses handles each request when the
device raises it:** the request lead, on the device's clock, before the
block's first output sample leaves. -/
theorem Builds.asked_of_const (hB : m.Builds f d w) {r : Fin R}
    (hc : ∀ s t, d.hostPaused (w.host r) s = d.hostPaused (w.host r) t) (b : ℕ) :
    d.deviceReading (some (m.device r)) ((w.speaker r).out ((w.speaker r).first b))
      - d.deviceReading (some (m.device r)) ((w.speaker r).asked b) = m.lead := by
  obtain ⟨ρ, v, hρ, hv, h⟩ := hB.speaker_asked r b
  rw [h, hv.unique (isBacklog_zero_of_const hc _), add_zero]
  exact hρ

end Unisono.Spec.GenerativeWorld
