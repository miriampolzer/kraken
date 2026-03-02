/-
Kraken - Example Programs (Experimental)

Advanced examples requiring Lean 4.28.0+ tactics.

For basic examples, see Kraken/Examples.lean.
-/

import KrakenExp.Tactics

-- Example using fine-grained tactics (step_match, step_instr, step_cps_v2)
-- This example benefits from the advanced SymM-based automation

def p11: Program := [
  (.none, .mov (.reg .rbx) (.imm 2)),    -- rbx := 2
  (.none, .adcx (.reg .rax) (.reg .rbx)) -- rax := rax + rbx
]

example (s_old: MachineState) (h_bound: (s_old.getReg .rax).toNat + 2 < 2^64):
    eventually p11 (fun s => (s.getReg .rax).toNat = (s_old.getReg .rax).toNat + 2) {s_old with rip := 0}
  := by
    delta p11
    -- First instruction
    step_cps_v2
    step_instr

    delta strt1
    step_match
    delta eval_operand eval_imm
    step_match
    delta set_reg_or_mem
    step_match
    delta MachineState.setReg
    dsimp (config := { beta := false, zeta := false, iota := true, proj := true, eta := false })

    step_cps_v2
    step_instr
    delta strt1
    step_match
    delta eval_reg_or_mem
    step_match
    dsimp (config := { beta := false, zeta := false, iota := true, proj := true, eta := false })
    -- NOTE: we still have nice let-bindings in the goal!
    delta MachineState.getReg Registers.get
    step_match
    -- JP: do we want rewrite rules here of the form:
    --   (s.setReg r1 v).getReg r1 == v
    --   (s.setReg r1 v).getReg r2 == s.getReg r2
    -- I also feel like there are too many helpers for getReg/setReg -- perhaps
    -- they need to be simplified.

    -- delta MachineState.setReg
    -- delta Registers.set
    -- dsimp (config := { beta := true, zeta := false, iota := false, proj := true, eta := false })
    sorry
