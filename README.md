# AXI in Lean 4

A layered, core-Lean-only (no Mathlib) model of the AMBA AXI4 protocol, with
proofs that the layers agree, and an executable golden model for cocotb.

Toolchain: `leanprover/lean4:v4.36.0` (see `lean-toolchain`). Build with
`lake build`; the library is `AXI`, the executable is `axi`.

## Layout

| File | Layer | Contents |
|---|---|---|
| `AXI/Types.lean` | payloads | `Burst`, `Resp`, `AddrBeat` (AW/AR), `WBeat n`, `BBeat`, `RBeat n` |
| `AXI/Handshake.lean` | cycle level | `Chan`, `Trace`, `SourceStable` (the SVA `valid && !ready \|=> valid && $stable(payload)`), `transfers` |
| `AXI/Burst.lean` | pure arithmetic | `beatAddr`, `WrapLegal`, `No4KCross`, `LenLegal`, `AddrLegal` (all decidable) |
| `AXI/Mem.lean` | memory | byte-addressed `Mem`, strobe-aware `writeBurst`, `doRead`, `writeResp` |
| `AXI/Slave.lean` | transaction level | `Txn`, `golden` (the golden model) |
| `AXI/Step.lean` | event level | `Slave.step`/`Slave.run`, refinement to `golden`, traces to events |
| `Main.lean` | executable | JSON-lines golden model (`axi [bus-width-bytes]`) |

## Main theorems

Handshake (`AXI/Handshake.lean`)
- `SourceStable.pending_persists`: under the source rule, a stalled beat is still presented unchanged `k` cycles later.
- `transfers_mono`, `transfers_length_le`: the transferred-beat list only grows, by at most one per cycle.

Burst arithmetic (`AXI/Burst.lean`)
- `beatAddr_zero`: beat 0 is the start address for every burst type.
- `wrap_in_window`: WRAP bursts never leave `[wrapLower, wrapLower + wrapTotal)`.
- `incr_mono`, `incr_in_window`: INCR addresses are monotone and stay within the aligned window.
- Concrete `decide` checks of WRAP4 and unaligned INCR sequences and of the 4 KB rule.

Memory (`AXI/Mem.lean`)
- `read_writeLanes_lt`, `read_writeLanes_outside`: strobed lanes are written, everything else is untouched.
- `doRead_last`, `doRead_id`, `doRead_length`: RLAST is set exactly on beat `len`, every beat carries the AR ID, `len + 1` beats.

Golden model (`AXI/Slave.lean`)
- `golden_bs`: the B stream is exactly one response per write, in issue order (write ordering).
- `golden_bs_filter_id`: the same restricted to one ID (per-ID ordering).
- `golden_rs_id`, `golden_rs_last`: the R stream is the AR bursts concatenated in order, with RLAST on each final beat.
- `golden_bs_getElem`: the `k`-th response depends only on the `k`-th write (response causality).

Refinement (`AXI/Step.lean`)
- `Slave.run_events_eq_golden`: the event-level slave, fed the events of a well-formed transaction list, emits exactly the golden model's B and R beats and ends in the golden memory with empty queues.
- `eventsUpTo_aw`, `eventsUpTo_w`, `eventsUpTo_ar`: the beats the slave sees from channel traces are exactly `transfers` of each trace.

## Golden model executable

```
lake build
printf '%s\n' \
  '{"ch":"aw","id":0,"addr":4096,"len":1,"size":2,"burst":"incr"}' \
  '{"ch":"w","data":"0xdeadbeef","strb":15,"last":false}' \
  '{"ch":"w","data":"0x01020304","strb":15,"last":true}' \
  '{"ch":"ar","id":1,"addr":4096,"len":1,"size":2,"burst":"incr"}' \
  | ./.lake/build/bin/axi 4
```

prints

```
{"ch":"b","id":0,"resp":"okay"}
{"ch":"r","data":"0xdeadbeef","id":1,"last":false,"resp":"okay"}
{"ch":"r","data":"0x01020304","id":1,"last":true,"resp":"okay"}
```

A cocotb monitor collects handshaked beats (what `transfers` computes), pipes
them in and compares the DUT's B/R beats against the output. A malformed W
burst (wrong beat count or WLAST position) gets `slverr`.

## Modelling decisions

- Byte lane `j` of a beat at address `a` maps to byte address `a / n * n + j`.
  The model writes exactly the WSTRB-selected lanes and reads all lanes back.
- AXI4 has no WID, so W data arrives in AW order; the event slave uses single
  AW and W FIFOs and completes the head write once `len + 1` beats are present.
  W beats may arrive before their AW.
- Read/write ordering is not specified by AXI without a dependency through the
  master, so the order of a `Txn` list is an input chosen by the testbench.
- Not yet modelled: AXI4-Lite as a separate variant (set `len = 0`), exclusive
  accesses, QoS/region/user signals, interconnect arbitration, and liveness.
