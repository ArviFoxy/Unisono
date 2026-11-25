/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.IdleView
public import Unisono.Solutions.Controller.Checked
public import Unisono.Solutions.Controller.Queries

/-!
# The clock exchanges of a host while nothing disturbs the stream

In a world built from a regular draw, let the stream to a speaker be
undisturbed from the true time `a₀` to `b₀` (`Draw.Undisturbed`), and let
the speaker's host handle a request by `b₀`. `queryDelay` and `streamDelay`
are the least delays of a clock query and of its answer.

* `recentExchange_of_undisturbed`: if the period began more than
  `exchangeWindow` before the request, on the host's clock, then every
  exchange that the host uses at the request was sent in the period and met
  no backlog: its three readings are those of the host's clock when the
  query was sent, of the sender's clock the query's least delay later, and
  of the host's clock the answer's least delay after that.
* `exists_exchange_of_undisturbed`: if the host's clock advanced by the
  polling period between a true time `T` of the period and an earlier
  request, and the least round trip has passed since that request, then the
  host's view holds such an exchange, sent between `T` and that request.
* `halfTrip_mem_of_undisturbed`: half of the round trip in use then lies
  between half of the least round trip times the least rate of the host's
  clock, cut to `tripCap`, and half of the least round trip times the
  largest rate.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld Unisono.Model.Descent

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} {p : FixedDelay.Params H} {rules : Rules H R}
  {q : LevelSettings} {share : ℝ} {kn : KnotSettings}

/-- **Every exchange that a host uses while nothing disturbs the stream met
no backlog.** In a world built from a regular draw, let the stream to
speaker `r` be undisturbed from `a₀` to `b₀`, let step `n` handle a request
of the speaker by `b₀`, and let the host's clock have advanced by more than
`exchangeWindow` from `a₀` to the request. Then every exchange that the host
uses at the request has a query sent at a true time `s₁` after `a₀`, with
the answer back before the request, and its readings are: the host's at
`s₁`, the sender's the least delay of a query later, and the host's the
least delay of the stream after that. -/
theorem recentExchange_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular)
    (hsender : p.sender = w.sender) (lookahead : ℕ+) {r : Fin R} (t : TimingSettings)
    {B : RateBands} {ρ : ℝ} {a₀ b₀ : Time}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀)
    (hwin : (w.clock (w.host r)).read a₀ + t.exchangeWindow
      < (w.clock (w.host r)).read ((w.speaker r).asked β))
    {x : Exchange}
    (hx : x ∈ recentExchanges t (((ruled p rules : Solution H R Payload).states w lookahead
      n).views (w.host r) ++ [w.askedEvent r β])) :
    ∃ s₁, a₀ < s₁
      ∧ s₁ + queryDelay f d w r + streamDelay f d w r < (w.speaker r).asked β
      ∧ x.sent = (w.clock (w.host r)).read s₁
      ∧ x.received = (w.clock w.sender).read (s₁ + queryDelay f d w r)
      ∧ x.arrived
        = (w.clock (w.host r)).read (s₁ + queryDelay f d w r + streamDelay f d w r) := by
  have hδq := queryDelay_pos hd f w r
  have hδs := streamDelay_pos hd f w r
  obtain ⟨e, hlast, hxv, hrec⟩ := mem_recentExchanges.mp hx
  rw [List.getLast?_concat] at hlast
  obtain rfl := Option.some.inj hlast
  have happ : exchangesOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
      (w.host r) ++ [w.askedEvent r β])
      = exchangesOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := exchangesOf_append_asked _ _ _ _ _
  rw [happ] at hxv
  obtain ⟨s₁, s₂, t₃, hsent, hrecv, harr, ⟨q₁, hd₁⟩, ⟨q₂, hd₂⟩, hbefore⟩ :=
    ruled_exchange p rules w hsender lookahead hxv
  have hnext := (ruled p rules : Solution H R Payload).askedNext_of_earliest w lookahead hE
  have ht₃ := hbefore r
  rw [hnext] at ht₃
  rw [hB.deliver] at hd₁ hd₂
  have e₁ : d.arrival f (w.host r) w.sender s₁ = s₂ := Option.some.inj hd₁
  have e₂ : d.arrival f w.sender (w.host r) s₂ = t₃ := Option.some.inj hd₂
  have hrd : (w.askedEvent r β : Event H R Payload).reading
      = (w.clock (w.host r)).read ((w.speaker r).asked β) := rfl
  rw [hrd, hsent] at hrec
  have hs₁ : a₀ < s₁ :=
    (w.clock (w.host r)).strictMono.lt_iff_lt.mp (by linarith)
  have hle₁ := hB.le_arrival (w.host r) w.sender s₁
  have hle₂ := hB.le_arrival w.sender (w.host r) s₂
  rw [e₁] at hle₁
  rw [e₂] at hle₂
  have hq : queryDelay f d w r = d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender :=
    rfl
  have hs : streamDelay f d w r = d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r) :=
    rfl
  have ha₁ := hB.arrival_eq_of_pathIdle (hd.linkPaused_monotone _ _) (hd.hostPaused_monotone _)
    (hd.hostPaused_monotone _) hU.backward hs₁.le (by linarith) (hd.leastDelay_pos f _ _).le
  rw [e₁] at ha₁
  have ha₂ := hB.arrival_eq_of_pathIdle (hd.linkPaused_monotone _ _) (hd.hostPaused_monotone _)
    (hd.hostPaused_monotone _) hU.forward (s := s₂) (by linarith) (by linarith)
    (hd.leastDelay_pos f _ _).le
  rw [e₂] at ha₂
  rw [← hq] at ha₁
  rw [← hs] at ha₂
  refine ⟨s₁, hs₁, by linarith, hsent, ?_, ?_⟩
  · rw [hrecv, ha₁]
  · rw [harr, ha₂, ha₁]

/-- **A clock exchange that meets no backlog is in the host's view.** In a
world built from a regular draw, in the setting `KnotSetting`, let the
stream to speaker `r`, on a host other than the sender's, be undisturbed
from `a₀` to `b₀`, and let step `n` handle a request of the speaker by
`b₀`. Let `T` be a true time from `a₀` on, and `β₁` a request of the
speaker at which the host's clock has advanced by at least the polling
period since `T`, handled more than the least round trip before the request
of step `n`. Then the host sent a clock query at a true time `s₁` from `T`
to the request `β₁`, and its view holds the exchange of that query: the
host's reading at `s₁`, the sender's the least delay of a query later, and
the host's the least delay of the stream after that. -/
theorem exists_exchange_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular)
    (hK : KnotSetting p rules w (d.arrival f) q share kn) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) (hperiod : 0 ≤ p.period) {B : RateBands} {ρ : ℝ}
    {a₀ b₀ : Time} (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀) {T : Time} {β₁ : ℕ} (hT : a₀ ≤ T)
    (hβ₁ : (w.clock (w.host r)).read T + p.period
      ≤ (w.clock (w.host r)).read ((w.speaker r).asked β₁))
    (hdone : (w.speaker r).asked β₁ + queryDelay f d w r + streamDelay f d w r
      < (w.speaker r).asked β) :
    ∃ s₁, T ≤ s₁ ∧ s₁ ≤ (w.speaker r).asked β₁
      ∧ (⟨(w.clock (w.host r)).read s₁,
            (w.clock w.sender).read (s₁ + queryDelay f d w r),
            (w.clock (w.host r)).read (s₁ + queryDelay f d w r + streamDelay f d w r)⟩ :
          Exchange)
        ∈ exchangesOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
          (w.host r) ++ [w.askedEvent r β]) := by
  have hδq := queryDelay_pos hd f w r
  have hδs := streamDelay_pos hd f w r
  have hsender := hK.noLoss.sender
  obtain ⟨n₁, s, r', outs, st, hn, hask, hTs, hsb⟩ := FixedDelay.exists_query p w lookahead
    hK.handed hK.asked hperiod r (by rw [hsender]; exact hr) hβ₁
  have harr₁ : d.arrival f (w.host r) w.sender s = s + queryDelay f d w r :=
    hB.arrival_eq_of_pathIdle (hd.linkPaused_monotone _ _) (hd.hostPaused_monotone _)
      (hd.hostPaused_monotone _) hU.backward (hT.trans hTs)
      (by
        show s + queryDelay f d w r ≤ b₀
        linarith) (hd.leastDelay_pos f _ _).le
  have harr₂ : d.arrival f w.sender (w.host r) (s + queryDelay f d w r)
      = s + queryDelay f d w r + streamDelay f d w r :=
    hB.arrival_eq_of_pathIdle (hd.linkPaused_monotone _ _) (hd.hostPaused_monotone _)
      (hd.hostPaused_monotone _) hU.forward (by linarith [hT.trans hTs])
      (by
        show s + queryDelay f d w r + streamDelay f d w r ≤ b₀
        linarith) (hd.leastDelay_pos f _ _).le
  have hstrict : ∀ s', s < s' →
      d.arrival f (w.host r) w.sender s < d.arrival f (w.host r) w.sender s' := by
    intro s' hs'
    rw [harr₁]
    have h1 := hB.le_arrival (w.host r) w.sender s'
    have h2 : queryDelay f d w r
        = d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender := rfl
    linarith
  have hmore := ruled_sendsMore (R := R) p rules
  have htime : (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w lookahead n
      = (w.speaker r).asked β := by
    rw [← Solution.eventTime_forget w Payload.plain lookahead hmore n]
    exact (ruled p rules : Solution H R Payload).handled_time w lookahead
      ((ruled p rules : Solution H R Payload).handled_of_asked w lookahead hE)
  have hex : (⟨(w.clock (w.host r)).read s,
        (w.clock w.sender).read (d.arrival f (w.host r) w.sender s),
        (w.clock (w.host r)).read
          (d.arrival f w.sender (w.host r) (d.arrival f (w.host r) w.sender s))⟩ : Exchange)
      ∈ plainExchangesOf (((FixedDelay.solution p :
          Solution H R FixedDelay.Payload).states w lookahead n).views (w.host r)) :=
    FixedDelay.exchange_of_query_before p w lookahead (A := fun i j s => d.arrival f i j s)
      (fun i j s q => hB.deliver i j s q) hsender hK.noLoss.copies hn hask hstrict (k' := n)
      (by
        show d.arrival f w.sender (w.host r) (d.arrival f (w.host r) w.sender s) < _
        rw [htime, harr₁, harr₂]
        linarith)
  rw [harr₁, harr₂] at hex
  have happ : exchangesOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
      (w.host r) ++ [w.askedEvent r β])
      = exchangesOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := exchangesOf_append_asked _ _ _ _ _
  refine ⟨s, hTs, hsb, ?_⟩
  rw [happ, exchangesOf_eq, Solution.views_forget w Payload.plain lookahead hmore n (w.host r)]
  exact hex

/-- **Half of the round trip in use while nothing disturbs the stream.** In
the setting of `recentExchange_of_undisturbed`, let the host use at least one
exchange at the request. Then half of the round trip in use is at least half
of the smaller of `tripCap` and the least round trip times the least rate of
the host's clock, and at most half of the least round trip times the largest
rate of the host's clock. -/
theorem halfTrip_mem_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular)
    (hsender : p.sender = w.sender) (lookahead : ℕ+) {r : Fin R} (t : TimingSettings)
    {B : RateBands} {ρ : ℝ} {a₀ b₀ : Time}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    {n β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hβ : (w.speaker r).asked β ≤ b₀)
    (hwin : (w.clock (w.host r)).read a₀ + t.exchangeWindow
      < (w.clock (w.host r)).read ((w.speaker r).asked β))
    (hne : recentExchanges t (((ruled p rules : Solution H R Payload).states w lookahead
      n).views (w.host r) ++ [w.askedEvent r β]) ≠ []) :
    halfTrip t (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r) ++ [w.askedEvent r β])
      ∈ Set.Icc (min (B.hostLo * (queryDelay f d w r + streamDelay f d w r)) t.tripCap / 2)
        (B.hostHi * (queryDelay f d w r + streamDelay f d w r) / 2) := by
  have hδq := queryDelay_pos hd f w r
  have hδs := streamDelay_pos hd f w r
  have hall : ∀ x ∈ recentExchanges t (((ruled p rules : Solution H R Payload).states w
        lookahead n).views (w.host r) ++ [w.askedEvent r β]),
      B.hostLo * (queryDelay f d w r + streamDelay f d w r) ≤ x.roundTrip
        ∧ x.roundTrip ≤ B.hostHi * (queryDelay f d w r + streamDelay f d w r) := by
    intro x hx
    obtain ⟨s₁, hs₁, hdone, hsent, -, harr⟩ :=
      recentExchange_of_undisturbed hB hd hsender lookahead t hU hE hβ hwin hx
    obtain ⟨h1, h2⟩ := hU.host_sub hd (y := s₁)
      (y' := s₁ + queryDelay f d w r + streamDelay f d w r) hs₁.le (by linarith)
      (by linarith)
    rw [← hB.clock, ← hB.clock] at h1 h2
    unfold Exchange.roundTrip
    rw [hsent, harr]
    have e : s₁ + queryDelay f d w r + streamDelay f d w r - s₁
        = queryDelay f d w r + streamDelay f d w r := by ring
    rw [e] at h1 h2
    exact ⟨h1, h2⟩
  constructor
  · exact le_halfTrip t hne fun x hx => (hall x hx).1
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    have h1 := (hall x hx).1
    have h2 := (hall x hx).2
    have h0 : 0 ≤ x.roundTrip :=
      (mul_nonneg hBv.host_pos.le (by linarith)).trans h1
    have h3 := halfTrip_le_of_mem t hx h0
    linarith

end Unisono.Solutions.Controller
