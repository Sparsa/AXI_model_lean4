/-!
# Cycle-level handshake model

A channel at one cycle is a `Chan α`: VALID, READY and the payload.
A channel trace is `Nat → Chan α`.  `SourceStable` is the AXI source rule
(`valid && !ready |=> valid && $stable(payload)` in SVA), and `transfers`
projects a trace to the list of beats that actually handshake.  That list
is what the transaction-level model consumes.
-/

namespace AXI

structure Chan (α : Type) where
  valid   : Bool
  ready   : Bool
  payload : α

namespace Chan

def fires (c : Chan α) : Bool := c.valid && c.ready

@[simp] theorem fires_iff (c : Chan α) :
    c.fires = true ↔ c.valid = true ∧ c.ready = true := by
  simp [fires]

end Chan

/-- A channel trace: the state of the channel at every cycle. -/
abbrev Trace (α : Type) := Nat → Chan α

/-- Source rule: VALID, once raised, holds with a stable payload until the handshake. -/
def SourceStable (tr : Trace α) : Prop :=
  ∀ t, (tr t).valid = true → (tr t).ready = false →
    (tr (t+1)).valid = true ∧ (tr (t+1)).payload = (tr t).payload

/-- The beats a channel trace transfers in cycles `[0, t)`. -/
def transfers (tr : Trace α) : Nat → List α
  | 0     => []
  | t + 1 => transfers tr t ++ (if (tr t).fires then [(tr t).payload] else [])

@[simp] theorem transfers_zero (tr : Trace α) : transfers tr 0 = [] := rfl

theorem transfers_succ (tr : Trace α) (t : Nat) :
    transfers tr (t+1) = transfers tr t ++ (if (tr t).fires then [(tr t).payload] else []) := rfl

theorem transfers_succ_fires (tr : Trace α) (t : Nat) (h : (tr t).fires = true) :
    transfers tr (t+1) = transfers tr t ++ [(tr t).payload] := by
  simp [transfers_succ, h]

theorem transfers_succ_idle (tr : Trace α) (t : Nat) (h : (tr t).fires = false) :
    transfers tr (t+1) = transfers tr t := by
  simp [transfers_succ, h]

/-- `transfers` is monotone: an earlier prefix is a prefix of a later one. -/
theorem transfers_mono (tr : Trace α) (s t : Nat) (h : s ≤ t) :
    ∃ l, transfers tr t = transfers tr s ++ l := by
  induction t with
  | zero =>
    have : s = 0 := Nat.le_zero.mp h
    subst this; exact ⟨[], rfl⟩
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · obtain ⟨l, hl⟩ := ih (Nat.le_of_lt_succ hlt)
      exact ⟨l ++ (if (tr t).fires then [(tr t).payload] else []),
             by rw [transfers_succ, hl, List.append_assoc]⟩
    · subst heq; exact ⟨[], by simp⟩

/-- Number of beats transferred is at most the number of cycles. -/
theorem transfers_length_le (tr : Trace α) (t : Nat) :
    (transfers tr t).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [transfers_succ, List.length_append]
    split <;> simp <;> omega

/-- Under `SourceStable`, a pending (VALID, not READY) beat is still presented,
    unchanged, `k` cycles later as long as it has not fired in between. -/
theorem SourceStable.pending_persists (tr : Trace α) (hs : SourceStable tr) (t k : Nat)
    (hv : (tr t).valid = true)
    (hstall : ∀ j, j < k → (tr (t + j)).ready = false) :
    (tr (t + k)).valid = true ∧ (tr (t + k)).payload = (tr t).payload := by
  induction k with
  | zero => exact ⟨hv, rfl⟩
  | succ k ih =>
    have hk := ih (fun j hj => hstall j (Nat.lt_succ_of_lt hj))
    have hr := hstall k (Nat.lt_succ_self k)
    have := hs (t + k) hk.1 hr
    rw [Nat.add_succ]
    exact ⟨this.1, this.2.trans hk.2⟩

end AXI
