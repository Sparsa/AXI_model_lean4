import AXI.Slave
import AXI.Handshake

/-!
# Event-level slave and refinement

The event-level slave consumes one handshaked beat at a time (`Event`) and
emits B and R beats as soon as it can.  It buffers AW beats and W beats in
FIFOs, as AXI4 requires W data to arrive in AW order (there is no WID), and
completes a write once the head AW has `len + 1` W beats available.

The refinement theorem `run_events_eq_golden` shows that, fed the events of
a transaction list, it produces exactly what `golden` produces.
-/

namespace AXI

inductive Event (n : Nat)
  | aw (a : AddrBeat)
  | w  (w : WBeat n)
  | ar (a : AddrBeat)

structure Slave (n : Nat) where
  mem  : Mem
  awq  : List AddrBeat
  wbuf : List (WBeat n)

structure StepOut (n : Nat) where
  slave : Slave n
  bs    : List BBeat
  rs    : List (RBeat n)

namespace Slave

def init (m : Mem) : Slave n := ⟨m, [], []⟩

@[simp] theorem init_mem (m : Mem) : (init (n := n) m).mem = m := rfl

/-- Complete the head write if all its data has arrived. -/
def tryWrite (s : Slave n) : Slave n × List BBeat :=
  match s.awq with
  | [] => (s, [])
  | a :: as =>
    if a.len + 1 ≤ s.wbuf.length then
      let ws := s.wbuf.take (a.len + 1)
      (⟨writeBurst s.mem a ws, as, s.wbuf.drop (a.len + 1)⟩, [writeResp a ws])
    else (s, [])

def step (s : Slave n) : Event n → StepOut n
  | .aw a =>
    let r := tryWrite ⟨s.mem, s.awq ++ [a], s.wbuf⟩
    ⟨r.1, r.2, []⟩
  | .w w =>
    let r := tryWrite ⟨s.mem, s.awq, s.wbuf ++ [w]⟩
    ⟨r.1, r.2, []⟩
  | .ar a => ⟨s, [], doRead n s.mem a⟩

def run (s : Slave n) : List (Event n) → StepOut n
  | [] => ⟨s, [], []⟩
  | e :: es =>
    let o1 := step s e
    let o2 := run o1.slave es
    ⟨o2.slave, o1.bs ++ o2.bs, o1.rs ++ o2.rs⟩

theorem run_append (s : Slave n) (es1 es2 : List (Event n)) :
    run s (es1 ++ es2) =
      let o1 := run s es1
      let o2 := run o1.slave es2
      ⟨o2.slave, o1.bs ++ o2.bs, o1.rs ++ o2.rs⟩ := by
  induction es1 generalizing s with
  | nil => simp [run]
  | cons e es ih => simp [run, ih, List.append_assoc]

/-- **Write-response causality**, event-level: the slave never emits a B beat
    for an AW it has not received.  More precisely every B response emitted
    carries the ID of some AW in the queue or in the event. -/
theorem step_aw_no_wdata (s : Slave n) (a : AddrBeat) (h : s.awq = []) (hw : s.wbuf = []) :
    step s (.aw a) = ⟨⟨s.mem, [a], []⟩, [], []⟩ := by
  simp [step, tryWrite, h, hw]

end Slave

/-! ## Events of a transaction list -/

def Txn.events : Txn n → List (Event n)
  | .write a ws => .aw a :: ws.map .w
  | .read a => [.ar a]

def eventsOf (ts : List (Txn n)) : List (Event n) := ts.flatMap Txn.events

/-- Every write transaction supplies exactly `len + 1` W beats. -/
def WFTxns : List (Txn n) → Prop
  | [] => True
  | .write a ws :: ts => ws.length = a.len + 1 ∧ WFTxns ts
  | .read _ :: ts => WFTxns ts

namespace Slave

/-- Feeding the remaining W beats of a burst to a slave that holds its AW
    and the earlier beats completes the write exactly on the last beat. -/
theorem run_wbeats (m : Mem) (a : AddrBeat) (pre rest : List (WBeat n))
    (hne : rest ≠ []) (hlen : pre.length + rest.length = a.len + 1) :
    run ⟨m, [a], pre⟩ (rest.map .w) =
      ⟨⟨writeBurst m a (pre ++ rest), [], []⟩, [writeResp a (pre ++ rest)], []⟩ := by
  induction rest generalizing pre with
  | nil => exact absurd rfl hne
  | cons w rest ih =>
    cases rest with
    | nil =>
      have hl : (pre ++ [w]).length ≤ a.len + 1 := by simp; simp at hlen; omega
      have hle : a.len ≤ pre.length := by simp at hlen; omega
      simp [run, step, tryWrite, hle, List.take_of_length_le hl, List.drop_of_length_le hl]
    | cons w' rest' =>
      have hlt : ¬ (a.len + 1 ≤ (pre ++ [w]).length) := by simp; simp at hlen; omega
      have := ih (pre ++ [w]) (by simp) (by simp; simp at hlen; omega)
      rw [List.append_assoc, List.singleton_append] at this
      rw [List.map_cons, run]
      simp only [step, tryWrite]
      simp only [hlt, ite_false]
      rw [this]
      simp

/-- A whole write transaction from the idle state. -/
theorem run_write (m : Mem) (a : AddrBeat) (ws : List (WBeat n)) (h : ws.length = a.len + 1) :
    run (init m) (Txn.events (.write a ws)) =
      ⟨init (writeBurst m a ws), [writeResp a ws], []⟩ := by
  have hne : ws ≠ [] := by intro hw; subst hw; simp at h
  have hstep : step (init m) (.aw a) = ⟨⟨m, [a], []⟩, [], []⟩ :=
    step_aw_no_wdata (n := n) (init m) a rfl rfl
  simp only [Txn.events, run, hstep]
  have := run_wbeats m a [] ws hne (by simpa using h)
  simp only [List.nil_append] at this
  simp [this, init]

/-- **Refinement.** The event-level slave, fed the events of a well-formed
    transaction list, emits exactly the golden model's B and R beats and ends
    with the golden model's memory and empty queues. -/
theorem run_events_eq_golden (m : Mem) (ts : List (Txn n)) (hwf : WFTxns ts) :
    run (init m) (eventsOf ts) =
      ⟨init (golden m ts).mem, (golden m ts).bs, (golden m ts).rs⟩ := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | write a ws =>
      obtain ⟨hlen, hwf'⟩ := hwf
      rw [eventsOf, List.flatMap_cons, run_append, run_write m a ws hlen]
      simp only [eventsOf] at ih
      simp [ih _ hwf', golden]
    | read a =>
      simp only [eventsOf, List.flatMap_cons, Txn.events, List.singleton_append, run, step]
      simp only [eventsOf] at ih
      simp [ih _ hwf, golden]

end Slave

/-! ## From channel traces to events

Given AW, W and AR channel traces, the events of one cycle are the beats that
handshake in that cycle.  `eventsUpTo` collects them over `[0, t)`, and the
beats it carries on each channel are exactly `transfers` of that channel's
trace, which is what ties the cycle-level model to the slave. -/

structure Traces (n : Nat) where
  aw : Trace AddrBeat
  w  : Trace (WBeat n)
  ar : Trace AddrBeat

def eventsAt (tr : Traces n) (t : Nat) : List (Event n) :=
  (if (tr.aw t).fires then [.aw (tr.aw t).payload] else []) ++
  (if (tr.w t).fires  then [.w  (tr.w t).payload]  else []) ++
  (if (tr.ar t).fires then [.ar (tr.ar t).payload] else [])

def eventsUpTo (tr : Traces n) : Nat → List (Event n)
  | 0 => []
  | t + 1 => eventsUpTo tr t ++ eventsAt tr (t + 1 - 1)

@[simp] def Event.awBeat : Event n → Option AddrBeat
  | .aw a => some a
  | .w _  => none
  | .ar _ => none

@[simp] def Event.wBeat : Event n → Option (WBeat n)
  | .aw _ => none
  | .w x  => some x
  | .ar _ => none

@[simp] def Event.arBeat : Event n → Option AddrBeat
  | .aw _ => none
  | .w _  => none
  | .ar a => some a

theorem eventsAt_aw (tr : Traces n) (t : Nat) :
    (eventsAt tr t).filterMap Event.awBeat = (if (tr.aw t).fires then [(tr.aw t).payload] else []) := by
  simp only [eventsAt, List.filterMap_append]
  split <;> split <;> split <;> simp [List.filterMap_cons]

theorem eventsAt_w (tr : Traces n) (t : Nat) :
    (eventsAt tr t).filterMap Event.wBeat = (if (tr.w t).fires then [(tr.w t).payload] else []) := by
  simp only [eventsAt, List.filterMap_append]
  split <;> split <;> split <;> simp [List.filterMap_cons]

theorem eventsAt_ar (tr : Traces n) (t : Nat) :
    (eventsAt tr t).filterMap Event.arBeat = (if (tr.ar t).fires then [(tr.ar t).payload] else []) := by
  simp only [eventsAt, List.filterMap_append]
  split <;> split <;> split <;> simp [List.filterMap_cons]

/-- The AW beats delivered to the slave are exactly the AW channel's transfers. -/
theorem eventsUpTo_aw (tr : Traces n) (t : Nat) :
    (eventsUpTo tr t).filterMap Event.awBeat = transfers tr.aw t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [eventsUpTo, List.filterMap_append, ih, eventsAt_aw, transfers_succ]

theorem eventsUpTo_w (tr : Traces n) (t : Nat) :
    (eventsUpTo tr t).filterMap Event.wBeat = transfers tr.w t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [eventsUpTo, List.filterMap_append, ih, eventsAt_w, transfers_succ]

theorem eventsUpTo_ar (tr : Traces n) (t : Nat) :
    (eventsUpTo tr t).filterMap Event.arBeat = transfers tr.ar t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [eventsUpTo, List.filterMap_append, ih, eventsAt_ar, transfers_succ]

end AXI
