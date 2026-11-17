import AXI.Types

/-!
# Burst address arithmetic (AMBA AXI spec A3.4.1)

`beatAddr b i` is the address of beat `i` of burst `b`.  The nonlinear
pieces (`2 ^ size`, the wrap window) are wrapped in definitions so that
`omega` can treat them as opaque atoms.
-/

namespace AXI

def bytesPerBeat (b : AddrBeat) : Nat := 2 ^ b.size

/-- Total bytes in the burst; for WRAP this is the size of the wrap window. -/
def wrapTotal (b : AddrBeat) : Nat := (b.len + 1) * bytesPerBeat b

/-- Lower boundary of the wrap window. -/
def wrapLower (b : AddrBeat) : Nat := b.addr / wrapTotal b * wrapTotal b

/-- Start address aligned down to the beat size. -/
def alignedAddr (b : AddrBeat) : Nat := b.addr / bytesPerBeat b * bytesPerBeat b

def beatAddr (b : AddrBeat) (i : Nat) : Nat :=
  match b.burst with
  | .fixed => b.addr
  | .incr  => if i = 0 then b.addr else alignedAddr b + i * bytesPerBeat b
  | .wrap  => wrapLower b + (b.addr + i * bytesPerBeat b - wrapLower b) % wrapTotal b

theorem bytesPerBeat_pos (b : AddrBeat) : 0 < bytesPerBeat b :=
  Nat.two_pow_pos _

theorem wrapTotal_pos (b : AddrBeat) : 0 < wrapTotal b :=
  Nat.mul_pos (Nat.succ_pos _) (bytesPerBeat_pos b)

theorem wrapLower_le (b : AddrBeat) : wrapLower b ≤ b.addr :=
  Nat.div_mul_le_self _ _

theorem wrapLower_add_mod (b : AddrBeat) : wrapLower b + b.addr % wrapTotal b = b.addr :=
  Nat.div_add_mod' _ _

theorem lt_wrapLower_add (b : AddrBeat) : b.addr < wrapLower b + wrapTotal b := by
  have := Nat.mod_lt b.addr (wrapTotal_pos b)
  have := wrapLower_add_mod b
  omega

theorem alignedAddr_le (b : AddrBeat) : alignedAddr b ≤ b.addr :=
  Nat.div_mul_le_self _ _

theorem alignedAddr_add_mod (b : AddrBeat) : alignedAddr b + b.addr % bytesPerBeat b = b.addr :=
  Nat.div_add_mod' _ _

theorem lt_alignedAddr_add (b : AddrBeat) : b.addr < alignedAddr b + bytesPerBeat b := by
  have := Nat.mod_lt b.addr (bytesPerBeat_pos b)
  have := alignedAddr_add_mod b
  omega

/-- Beat 0 is always the start address, whatever the burst type. -/
theorem beatAddr_zero (b : AddrBeat) : beatAddr b 0 = b.addr := by
  unfold beatAddr
  cases b.burst with
  | fixed => rfl
  | incr => simp
  | wrap =>
    have h1 := wrapLower_le b
    have h2 := lt_wrapLower_add b
    have h3 : (b.addr - wrapLower b) % wrapTotal b = b.addr - wrapLower b :=
      Nat.mod_eq_of_lt (by omega)
    simp only [Nat.zero_mul, Nat.add_zero, h3]
    omega

/-- FIXED bursts never move. -/
theorem beatAddr_fixed (b : AddrBeat) (h : b.burst = .fixed) (i : Nat) :
    beatAddr b i = b.addr := by
  simp [beatAddr, h]

/-- WRAP bursts never leave their wrap window. -/
theorem wrap_in_window (b : AddrBeat) (h : b.burst = .wrap) (i : Nat) :
    wrapLower b ≤ beatAddr b i ∧ beatAddr b i < wrapLower b + wrapTotal b := by
  have hlt := Nat.mod_lt (b.addr + i * bytesPerBeat b - wrapLower b) (wrapTotal_pos b)
  simp only [beatAddr, h]
  omega

/-- INCR bursts are monotone after beat 0. -/
theorem incr_mono (b : AddrBeat) (h : b.burst = .incr) (i : Nat) :
    beatAddr b i ≤ beatAddr b (i+1) := by
  have hp := bytesPerBeat_pos b
  have ha := alignedAddr_le b
  have hal := lt_alignedAddr_add b
  simp only [beatAddr, h]
  cases i with
  | zero => simp; omega
  | succ i =>
    simp only [Nat.succ_ne_zero, ite_false]
    have : (i+1) * bytesPerBeat b ≤ (i+1+1) * bytesPerBeat b :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- Every beat of an INCR burst lies in `[addr, alignedAddr + (len+1)*bytes)`. -/
theorem incr_in_window (b : AddrBeat) (h : b.burst = .incr) (i : Nat) (hi : i ≤ b.len) :
    b.addr ≤ beatAddr b i ∧ beatAddr b i < alignedAddr b + wrapTotal b := by
  have hp := bytesPerBeat_pos b
  have ha := alignedAddr_le b
  have hal := lt_alignedAddr_add b
  have hwt : wrapTotal b = (b.len + 1) * bytesPerBeat b := rfl
  have h1 : 1 * bytesPerBeat b ≤ (b.len + 1) * bytesPerBeat b :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [beatAddr, h]
  split
  · subst_vars; omega
  · have : i * bytesPerBeat b < (b.len + 1) * bytesPerBeat b :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    constructor
    · have : 1 * bytesPerBeat b ≤ i * bytesPerBeat b :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · omega

/-! ## Legality predicates (A3.4.1) -/

/-- WRAP bursts: length 2, 4, 8 or 16 and start address aligned to the beat size. -/
def WrapLegal (b : AddrBeat) : Prop :=
  (b.len + 1 = 2 ∨ b.len + 1 = 4 ∨ b.len + 1 = 8 ∨ b.len + 1 = 16) ∧
  b.addr % bytesPerBeat b = 0

instance : DecidablePred WrapLegal := fun b => by
  unfold WrapLegal; infer_instance

/-- A burst must not cross a 4 KB boundary. -/
def No4KCross (b : AddrBeat) : Prop :=
  b.addr / 4096 = beatAddr b b.len / 4096

instance : DecidablePred No4KCross := fun b => by
  unfold No4KCross; infer_instance

/-- AXI4 bursts are at most 256 beats; FIXED and WRAP at most 16. -/
def LenLegal (b : AddrBeat) : Prop :=
  match b.burst with
  | .incr  => b.len < 256
  | .fixed => b.len < 16
  | .wrap  => b.len < 16

instance : DecidablePred LenLegal := fun b => by
  unfold LenLegal; cases b.burst <;> infer_instance

/-- A transaction the spec allows a master to issue. -/
def AddrLegal (b : AddrBeat) : Prop :=
  LenLegal b ∧ No4KCross b ∧ (b.burst = .wrap → WrapLegal b)

instance : DecidablePred AddrLegal := fun b => by
  unfold AddrLegal; infer_instance

/-- A legal WRAP burst never crosses 4 KB, because its window is a power-of-two
    sized block of at most `16 * 128 = 2048` bytes aligned to its own size. -/
theorem wrap_window_aligned (b : AddrBeat) :
    wrapLower b % wrapTotal b = 0 := by
  unfold wrapLower
  exact Nat.mul_mod_left _ _

/-! ## Concrete checks -/

example : No4KCross ⟨0, 4064, 3, 3, .incr⟩ := by decide
example : ¬ No4KCross ⟨0, 4088, 3, 3, .incr⟩ := by decide
example : WrapLegal ⟨0, 0x1010, 3, 2, .wrap⟩ := by decide
example : ¬ WrapLegal ⟨0, 0x1011, 3, 2, .wrap⟩ := by decide

/-- WRAP4 of 4-byte beats starting at 0x1018 wraps 0x1018, 0x101C, 0x1010, 0x1014. -/
example : (List.range 4).map (beatAddr ⟨0, 0x1018, 3, 2, .wrap⟩) =
    [0x1018, 0x101C, 0x1010, 0x1014] := by decide

/-- INCR from an unaligned start aligns down from beat 1 onward. -/
example : (List.range 4).map (beatAddr ⟨0, 0x1001, 3, 2, .incr⟩) =
    [0x1001, 0x1004, 0x1008, 0x100C] := by decide

end AXI
