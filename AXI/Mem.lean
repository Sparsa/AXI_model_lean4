import AXI.Types
import AXI.Burst

/-!
# Byte-addressed memory and beat-level data movement

The data bus is `n` bytes wide.  Byte lane `j` of a beat whose address is
`a` corresponds to byte address `laneBase n a + j`, where `laneBase` aligns
`a` down to the bus width.  Which lanes carry data is decided by WSTRB
(writes) or by the master ignoring unused lanes (reads), so the model writes
exactly the strobed lanes and reads back all `n` lanes.
-/

namespace AXI

structure Mem where
  read : Nat → UInt8

namespace Mem

def write (m : Mem) (a : Nat) (v : UInt8) : Mem :=
  ⟨fun x => if x = a then v else m.read x⟩

def zero : Mem := ⟨fun _ => 0⟩

@[simp] theorem read_write_same (m : Mem) (a : Nat) (v : UInt8) :
    (m.write a v).read a = v := by
  simp [write]

@[simp] theorem read_write_other (m : Mem) (a x : Nat) (v : UInt8) (h : x ≠ a) :
    (m.write a v).read x = m.read x := by
  simp [write, h]

end Mem

/-- Base address of the bus-width chunk containing `a`. -/
def laneBase (n a : Nat) : Nat := a / n * n

/-- Byte lane `j` of a data beat. -/
def laneByte (data : BitVec (8 * n)) (j : Nat) : UInt8 :=
  UInt8.ofNat (data >>> (8 * j)).toNat

/-! ## Writes -/

/-- Write the first `k` lanes of `w` (those with WSTRB set) at `base`. -/
def writeLanes (m : Mem) (base : Nat) (w : WBeat n) : Nat → Mem
  | 0     => m
  | j + 1 =>
    let m' := writeLanes m base w j
    if w.strb.getLsbD j then m'.write (base + j) (laneByte w.data j) else m'

/-- Addresses outside `[base, base + k)` are untouched. -/
theorem read_writeLanes_outside (m : Mem) (base : Nat) (w : WBeat n) (k x : Nat)
    (hx : x < base ∨ base + k ≤ x) :
    (writeLanes m base w k).read x = m.read x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : x ≠ base + k := by omega
    have hx' : x < base ∨ base + k ≤ x := by omega
    simp only [writeLanes]
    split
    · rw [Mem.read_write_other _ _ _ _ hne]; exact ih hx'
    · exact ih hx'

/-- Lanes `j < k` read back as the strobed byte or the old contents. -/
theorem read_writeLanes_lt (m : Mem) (base : Nat) (w : WBeat n) (k j : Nat) (hj : j < k) :
    (writeLanes m base w k).read (base + j) =
      if w.strb.getLsbD j then laneByte w.data j else m.read (base + j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [writeLanes]
    by_cases hjk : j = k
    · subst hjk
      by_cases hs : w.strb.getLsbD j = true
      · simp [hs]
      · simp only [hs, Bool.false_eq_true, ite_false]
        exact read_writeLanes_outside m base w j (base + j) (Or.inr (Nat.le_refl _))
    · have hlt : j < k := by omega
      have hne : base + j ≠ base + k := by omega
      split
      · rw [Mem.read_write_other _ _ _ _ hne]; exact ih hlt
      · exact ih hlt

/-- Write beat `i` of burst `b`. -/
def writeBeat (m : Mem) (b : AddrBeat) (i : Nat) (w : WBeat n) : Mem :=
  writeLanes m (laneBase n (beatAddr b i)) w n

/-- Write beats `ws` of burst `b`, starting at beat index `i`. -/
def writeBurstFrom (m : Mem) (b : AddrBeat) : Nat → List (WBeat n) → Mem
  | _, []      => m
  | i, w :: ws => writeBurstFrom (writeBeat m b i w) b (i + 1) ws

def writeBurst (m : Mem) (b : AddrBeat) (ws : List (WBeat n)) : Mem :=
  writeBurstFrom m b 0 ws

/-- Lane `j` of beat `i` after a burst write: the strobed byte of the *last*
    beat that targets that chunk, which for INCR/WRAP bursts with distinct
    beat addresses is beat `i` itself.  Stated here for the simplest case,
    a single-beat burst. -/
theorem read_writeBurst_single (m : Mem) (b : AddrBeat) (w : WBeat n) (j : Nat) (hj : j < n) :
    (writeBurst m b [w]).read (laneBase n (beatAddr b 0) + j) =
      if w.strb.getLsbD j then laneByte w.data j
      else m.read (laneBase n (beatAddr b 0) + j) := by
  simp only [writeBurst, writeBurstFrom, writeBeat]
  exact read_writeLanes_lt m _ w n j hj

/-! ## Reads -/

/-- Assemble the first `k` lanes at `base` into a data word. -/
def readLanes (n : Nat) (m : Mem) (base : Nat) : Nat → BitVec (8 * n)
  | 0     => 0
  | j + 1 => readLanes n m base j ||| ((m.read (base + j)).toBitVec.setWidth (8 * n) <<< (8 * j))

def readBeat (n : Nat) (m : Mem) (b : AddrBeat) (i : Nat) : BitVec (8 * n) :=
  readLanes n m (laneBase n (beatAddr b i)) n

/-- RLAST pattern for a burst of `len + 1` beats: true exactly on the final beat. -/
def lastPattern (len : Nat) : List Bool :=
  (List.range (len + 1)).map fun i => decide (i = len)

def doRead (n : Nat) (m : Mem) (b : AddrBeat) : List (RBeat n) :=
  (List.range (b.len + 1)).map fun i =>
    ⟨b.id, readBeat n m b i, .okay, decide (i = b.len)⟩

@[simp] theorem doRead_length (n : Nat) (m : Mem) (b : AddrBeat) :
    (doRead n m b).length = b.len + 1 := by
  simp [doRead]

/-- Every R beat carries the request ID. -/
theorem doRead_id (n : Nat) (m : Mem) (b : AddrBeat) :
    (doRead n m b).map (·.id) = List.replicate (b.len + 1) b.id := by
  simp [doRead, List.map_map, Function.comp_def, List.map_const']

/-- RLAST is set exactly on beat `len`. -/
theorem doRead_last (n : Nat) (m : Mem) (b : AddrBeat) :
    (doRead n m b).map (·.last) = lastPattern b.len := by
  simp [doRead, lastPattern, List.map_map, Function.comp_def]

/-- Beat `i` of the read data is the memory contents at that beat's chunk. -/
theorem doRead_getElem (n : Nat) (m : Mem) (b : AddrBeat) (i : Nat) (hi : i < b.len + 1) :
    (doRead n m b)[i]'(by simp [hi]) = ⟨b.id, readBeat n m b i, .okay, decide (i = b.len)⟩ := by
  simp [doRead]

/-- Every read response is OKAY: this slave never faults. -/
theorem doRead_resp (n : Nat) (m : Mem) (b : AddrBeat) :
    ∀ r ∈ doRead n m b, r.resp = .okay := by
  intro r hr
  simp [doRead] at hr
  obtain ⟨i, _, rfl⟩ := hr
  rfl

/-! ## Write-data well-formedness and the write response -/

/-- A W burst is well formed when it has `len + 1` beats and WLAST is set
    exactly on the final one. -/
def wBurstOk (b : AddrBeat) (ws : List (WBeat n)) : Bool :=
  ws.map (·.last) == lastPattern b.len

theorem wBurstOk_length (b : AddrBeat) (ws : List (WBeat n)) (h : wBurstOk b ws = true) :
    ws.length = b.len + 1 := by
  have h' : ws.map (·.last) = lastPattern b.len := by
    unfold wBurstOk at h; exact beq_iff_eq.mp h
  have := congrArg List.length h'
  simpa [lastPattern] using this

/-- The B response: OKAY for a well-formed burst, SLVERR otherwise. -/
def writeResp (b : AddrBeat) (ws : List (WBeat n)) : BBeat :=
  ⟨b.id, if wBurstOk b ws then .okay else .slverr⟩

@[simp] theorem writeResp_id (b : AddrBeat) (ws : List (WBeat n)) :
    (writeResp b ws).id = b.id := rfl

def applyWrite (m : Mem) (b : AddrBeat) (ws : List (WBeat n)) : Mem × BBeat :=
  (writeBurst m b ws, writeResp b ws)

end AXI
