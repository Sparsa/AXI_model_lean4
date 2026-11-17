import Lean.Data.Json
import AXI

/-!
# `axi`: golden-model executable

Reads handshaked beats as JSON lines on stdin and writes the expected B and R
beats as JSON lines on stdout, one per beat, as soon as the slave emits them.

    axi [data-width-in-bytes]      (default 4)

Input lines:

    {"ch":"aw","id":0,"addr":4096,"len":3,"size":2,"burst":"incr"}
    {"ch":"w","data":"0xdeadbeef","strb":15,"last":false}
    {"ch":"ar","id":1,"addr":4096,"len":3,"size":2,"burst":"incr"}

Output lines:

    {"ch":"b","id":0,"resp":"okay"}
    {"ch":"r","id":1,"data":"0xdeadbeef","resp":"okay","last":false}
-/

open Lean AXI

def AXI.Burst.ofString? : String → Option Burst
  | "fixed" => some .fixed
  | "incr"  => some .incr
  | "wrap"  => some .wrap
  | _ => none

def AXI.Resp.toString : Resp → String
  | .okay => "okay" | .exokay => "exokay" | .slverr => "slverr" | .decerr => "decerr"

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex? (s : String) : Option Nat :=
  let s := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  s.foldl (fun acc c => do let a ← acc; let d ← hexDigit? c; pure (a * 16 + d)) (some 0)

/-- Hex with `digits` digits, zero padded. -/
def toHex (digits v : Nat) : String :=
  let ds := Nat.toDigits 16 v
  "0x" ++ String.ofList (List.replicate (digits - ds.length) '0' ++ ds)

/-- A numeric field may be a JSON number or a hex string. -/
def getNum (j : Json) (k : String) : Except String Nat := do
  let v ← j.getObjVal? k
  match v with
  | .num _ => v.getNat?
  | .str s => match parseHex? s with
    | some n => pure n
    | none => throw s!"field {k}: bad hex string {s}"
  | _ => throw s!"field {k}: expected number or hex string"

def parseAddrBeat (j : Json) : Except String AddrBeat := do
  let burst ← j.getObjValAs? String "burst"
  let some b := Burst.ofString? burst | throw s!"bad burst {burst}"
  pure ⟨← getNum j "id", ← getNum j "addr", ← getNum j "len", ← getNum j "size", b⟩

def parseEvent (n : Nat) (j : Json) : Except String (Event n) := do
  match ← j.getObjValAs? String "ch" with
  | "aw" => return .aw (← parseAddrBeat j)
  | "ar" => return .ar (← parseAddrBeat j)
  | "w"  =>
    let data ← getNum j "data"
    let strb ← getNum j "strb"
    let last ← j.getObjValAs? Bool "last"
    return .w ⟨BitVec.ofNat _ data, BitVec.ofNat _ strb, last⟩
  | ch => throw s!"unknown channel {ch}"

def bToJson (b : BBeat) : Json :=
  Json.mkObj [("ch", "b"), ("id", b.id), ("resp", b.resp.toString)]

def rToJson (r : RBeat n) : Json :=
  Json.mkObj [("ch", "r"), ("id", r.id), ("data", toHex (2 * n) r.data.toNat),
              ("resp", r.resp.toString), ("last", r.last)]

partial def loop (n : Nat) (stdin stdout stderr : IO.FS.Stream) (s : Slave n) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if line.isEmpty then loop n stdin stdout stderr s else
  match Json.parse line >>= parseEvent n with
  | .error e =>
    stderr.putStrLn s!"axi: {e}: {line}"
    loop n stdin stdout stderr s
  | .ok ev =>
    let out := s.step ev
    for b in out.bs do stdout.putStrLn (bToJson b).compress
    for r in out.rs do stdout.putStrLn (rToJson r).compress
    stdout.flush
    loop n stdin stdout stderr out.slave

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 4
  if n = 0 then
    IO.eprintln "axi: data width must be positive"
    return 1
  loop n (← IO.getStdin) (← IO.getStdout) (← IO.getStderr) (Slave.init Mem.zero)
  return 0
