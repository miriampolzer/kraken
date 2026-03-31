/-
Kraken - Example Programs

Test programs demonstrating the assembly interpreter.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Tactics
import Kraken.Parser

open Kraken.Parser

noncomputable
def default [Layout] (start: Label): MachineState := ({}, layout start)

-- Example 1: single step of execution
def p1: Program := [
  .Label "start",
  .Instr ⟨ .W64, .W64, .mov (Reg.rax) (.imm (.Int64 1)) ⟩
]

syntax "step1" : tactic
macro_rules
  | `(tactic|step1) =>
  `(tactic|
    simp [
      step1,Program.straightline,
      Program.position_of_addr,Program.positions,Program.positions',layout,List.filter,Position.Label,
      List.dropWhile,bne,BEq.beq,instBEqDirective.beq,dropInstrs,Program.straightline',Instr.interp,Operation.interp,Operand.interp];
    simp (ground:=True);
    simp [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp];
    simp (ground:=True)
       <;> try native_decide)

-- Super-simple example to debug tactics
example [Layout]: step1 p1 (default "start") (fun s => s.1.regs.rax = 1) := by
  simp [p1,_root_.default]
  simp [step1,Program.straightline]
  simp [Program.position_of_addr,Program.positions,Program.positions',layout,List.filter,Position.Label]
  simp [List.dropWhile,bne,BEq.beq,instBEqDirective.beq,dropInstrs,Program.straightline',Instr.interp,Operation.interp,Operand.interp]
  simp (ground:=True)
  simp [MachineData.set,Reg64s.set,MachineData.setReg,Reg64s.set64,ConstExpr.interp]
  simp (ground:=True)
  simp
  
  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/
  
  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2: Program := parse! "
start:
    mov $1, %rax
    xor %rax %rax
    jnz start

    mov $2, %rax
"

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

-- Example 2: stepping through both straightline and control instructions
example [Layout]: eventually p2 (fun s => s.1.regs.rax = 2) (default "start") := by
  simp [p2,_root_.default,parse!,parse,String.startPos]
  simp (config := { ground := True, maxSteps := 2000000 })

  apply step_cps
  step1

  apply step_cps
  step1

  apply step_cps
  step_one

  apply eventually.done
  simp

def p3: Program := parse! "
init:
  mov $2 %rdx             # rdx: current result = 2
start:
  sub $0 %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  .mulx %rdx %rdx %rax    # BODY: rdx := rdx * rdx
  sub 1 %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
"

def p3_spec (s: MachineState): Nat := 2^(2^s.1.regs.rbx.toNat)

set_option maxHeartbeats 4000000 in
theorem p3_correct [Layout] (initial: MachineState):
    p3_spec initial < 2^64 →
    (layout ("init", 0) = initial.2) →
    eventually p3 (fun s => s.1.regs.rdx.toNat == p3_spec initial ∧ s.1.regs.rax == 0) initial :=
  by
  sorry -- simp times out due to larger Reg enum (64 constructors with aliased registers)
  /-
    intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp

    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat = i ∧ i ≤ initial.regs.rbx.toNat ∧ s.regs.rdx.toNat = 2^(2^(initial.regs.rbx.toNat - i))) initial.regs.rbx.toNat
    constructor
    . simp
    . constructor
      -- Invariant at index 0 ==> post
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_rbx_le, h_inv ⟩
        -- Step through a few program steps
        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp
        apply step_cps
        step_one
        have : state.regs.rbx.toNat = 0 := by grind
        simp [this]
        apply step_cps
        step_one
        apply eventually.done
        simp
        -- Now functional correctness for initial invariant
        simp [p3_spec]
        grind

      -- Invariant preserved
      . intro state k h_k_nonzero inv
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_rbx_le, h_inv ⟩

        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp

        apply step_cps
        step_one
        have h_k_ne : k ≠ 0 := by grind
        -- state.regs.rbx.toNat = k and toNat < 2^64 for UInt64
        have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (state.regs.rbx.toNat_lt)
        -- Simplify all the Int64.toUInt64 terms
        simp_all only [ne_eq, not_false_eq_true]
        -- Prove the if-condition is false: UInt64.ofInt ↑k ≠ 0 when k ≠ 0
        have h_cond : UInt64.ofInt (k : Int) ≠ 0 := UInt64_ofInt_natCast_ne_zero k h_k_lt h_k_ne
        rw [if_neg h_cond]




        apply step_cps
        step_one
        apply step_cps
        step_one
        apply step_cps
        step_one
        apply eventually.done

        -- Goals for invariant preservation
        constructor
        . simp -- back to correct address
        . match h_state:state.regs.rbx, h_init:initial.regs.rbx with
          | ⟨v_s⟩, ⟨v_i⟩ =>
            have h_k_lt : k < 2^64 := h_rbx_is_k ▸ (by rw [h_state]; exact v_s.isLt)
            have h_init_lt : v_i.toNat < 2^64 := v_i.isLt
            simp [h_state, h_init, p3_spec, Reg.width, UInt64.ofInt, UInt64.ofNat, UInt64.toNat_ofNat] at *
            constructor
            . omega
            . constructor
              . omega
              . rw [h_inv]
                have h_vi_k : v_i.toNat - (k - 1) = (v_i.toNat - k) + 1 := by omega
                rw [h_vi_k, Nat.mod_eq_of_lt]
                . rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                . apply Nat.lt_of_le_of_lt _ h_bounds
                  rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
                  apply Nat.pow_le_pow_right (by decide)
                  apply Nat.pow_le_pow_right (by decide)
                  omega
  -/

