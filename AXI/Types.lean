/-!
# AXI channel payload types

Transaction-level types for the five AXI channels (AW, W, B, AR, R).
`AddrBeat` is shared by AW and AR, since the two address channels carry
the same fields.
-/

namespace AXI

inductive Burst
  | fixed | incr | wrap
  deriving Repr, DecidableEq, Inhabited

inductive Resp
  | okay | exokay | slverr | decerr
  deriving Repr, DecidableEq, Inhabited

/-- AW / AR payload. -/
structure AddrBeat where
  id    : Nat
  addr  : Nat
  /-- AxLEN: number of beats minus one. -/
  len   : Nat
  /-- AxSIZE: bytes per beat is `2 ^ size`. -/
  size  : Nat
  burst : Burst
  deriving Repr, DecidableEq, Inhabited

/-- W payload, parameterised by the data width in bytes. -/
structure WBeat (n : Nat) where
  data : BitVec (8 * n)
  strb : BitVec n
  last : Bool
  deriving Repr, DecidableEq

/-- B payload. -/
structure BBeat where
  id   : Nat
  resp : Resp
  deriving Repr, DecidableEq, Inhabited

/-- R payload, parameterised by the data width in bytes. -/
structure RBeat (n : Nat) where
  id   : Nat
  data : BitVec (8 * n)
  resp : Resp
  last : Bool
  deriving Repr, DecidableEq

end AXI
