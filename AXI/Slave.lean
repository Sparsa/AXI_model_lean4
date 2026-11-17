import AXI.Mem

/-!
# Transaction-level golden model

A `Txn` is a complete write (AW beat plus its W beats) or a read (AR beat).
`golden` runs a list of transactions in order and returns the final memory
and the B and R beats, in the order the slave emits them.

AXI leaves the relative order of reads and writes unspecified unless the
master waits for the response, so the order of the `Txn` list is an input:
the testbench decides it (for example by completion cycle).
-/

namespace AXI

inductive Txn (n : Nat)
  | write (a : AddrBeat) (ws : List (WBeat n))
  | read  (a : AddrBeat)

structure Result (n : Nat) where
  mem : Mem
  bs  : List BBeat
  rs  : List (RBeat n)

def golden (m : Mem) : List (Txn n) → Result n
  | [] => ⟨m, [], []⟩
  | .write a ws :: ts =>
    let g := golden (writeBurst m a ws) ts
    ⟨g.mem, writeResp a ws :: g.bs, g.rs⟩
  | .read a :: ts =>
    let g := golden m ts
    ⟨g.mem, g.bs, doRead n m a ++ g.rs⟩

/-- The write transactions, in order. -/
def writesOf : List (Txn n) → List (AddrBeat × List (WBeat n))
  | [] => []
  | .write a ws :: ts => (a, ws) :: writesOf ts
  | .read _ :: ts => writesOf ts

/-- The read requests, in order. -/
def readsOf : List (Txn n) → List AddrBeat
  | [] => []
  | .write _ _ :: ts => readsOf ts
  | .read a :: ts => a :: readsOf ts

/-! ## Ordering -/

/-- **Write ordering.** The B channel carries exactly one response per write,
    in the order the writes were issued. -/
theorem golden_bs (m : Mem) (ts : List (Txn n)) :
    (golden m ts).bs = (writesOf ts).map fun p => writeResp p.1 p.2 := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [golden, writesOf, ih]

/-- **Per-ID write ordering.** Restricting to one ID, responses still come
    back in request order. -/
theorem golden_bs_filter_id (m : Mem) (ts : List (Txn n)) (i : Nat) :
    (golden m ts).bs.filter (·.id == i) =
      ((writesOf ts).filter (·.1.id == i)).map fun p => writeResp p.1 p.2 := by
  rw [golden_bs, List.filter_map]
  rfl

theorem golden_bs_length (m : Mem) (ts : List (Txn n)) :
    (golden m ts).bs.length = (writesOf ts).length := by
  simp [golden_bs]

/-- **Read ordering.** The R channel is the concatenation of each read's
    beats, in AR order; every beat carries its request's ID. -/
theorem golden_rs_id (m : Mem) (ts : List (Txn n)) :
    (golden m ts).rs.map (·.id) = (readsOf ts).flatMap fun a => List.replicate (a.len + 1) a.id := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [golden, readsOf, ih, doRead_id]

/-- **RLAST.** Across the whole R stream, RLAST marks exactly the final beat
    of each burst. -/
theorem golden_rs_last (m : Mem) (ts : List (Txn n)) :
    (golden m ts).rs.map (·.last) = (readsOf ts).flatMap fun a => lastPattern a.len := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [golden, readsOf, ih, doRead_last]

theorem golden_rs_length (m : Mem) (ts : List (Txn n)) :
    (golden m ts).rs.length = ((readsOf ts).map fun a => a.len + 1).sum := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [golden, readsOf, ih]

/-- **Write-response causality**, transaction-level form: the response to a
    write is a function of its own AW beat and W beats only, so it cannot be
    produced before they are known. -/
theorem golden_bs_getElem (m : Mem) (ts : List (Txn n)) (k : Nat) (hk : k < (writesOf ts).length) :
    (golden m ts).bs[k]'(by rw [golden_bs_length]; exact hk) =
      writeResp (writesOf ts)[k].1 (writesOf ts)[k].2 := by
  simp [golden_bs]

/-- A read of a chunk that no write in `ts` touched returns the original data. -/
theorem golden_mem_no_writes (m : Mem) (ts : List (Txn n)) (h : writesOf ts = []) :
    (golden m ts).mem = m := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | write => simp [writesOf] at h
    | read a => simp [writesOf] at h; simp [golden, ih m h]

end AXI
