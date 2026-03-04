/-
KrakenTest - Compare Kraken semantics against real x86 execution

Usage: krakentest <assembly.S> <as_output.bin>

Arguments:
- assembly.S: Assembly source file with test code
- as_output.bin: Binary file (136 bytes) from real x86 execution containing:
    - 16 registers (8 bytes each, little-endian): rax, rbx, ... r15
    - flags (8 bytes): CF at bit 0, ZF at bit 6, OF at bit 11
  This file is produced by running the assembled test which writes
  final register state to stdout via the capture epilogue.

Flow:
  1. Shell: assembly.S → as/ld → ./test > as_output.bin (real x86 execution)
  2. Lean: assembly.S → Parser.parse → Semantics.eval → expected MachineState
  3. Lean: as_output.bin → parseRegisterState → actual MachineState
  4. Lean: compare expected vs actual → PASS or FAIL with differences
-/

import Kraken.TestHarness

open Kraken.TestHarness

def main (args : List String) : IO UInt32 := do
  if args.length < 2 then
    IO.eprintln "Usage: krakentest <assembly.S> <as_output.bin>"
    return 1

  let asmFile := args[0]!
  let binFile := args[1]!

  -- Read assembly source and parse it for Kraken evaluation
  let asmCode ← IO.FS.readFile asmFile

  -- Read binary output from real x86 execution (136 bytes: registers + flags)
  let asOutput ← IO.FS.readBinFile binFile

  -- Compare Kraken's eval result against real x86 result (inside Lean)
  let result := runTest asmCode asOutput

  IO.println result.toString

  match result with
  | .success => return 0
  | _ => return 1
