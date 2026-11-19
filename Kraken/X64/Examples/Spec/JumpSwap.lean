module

import Kraken.X64.Spec
import Kraken.Tactics
import Kraken.X64.Parser

open Kraken (Layout)

namespace Spec.Examples.JumpSwap

attribute [local ksimp] Nat.shiftRight_zero BitVec.setWidth_eq BitVec.ofNat_toNat

def swapJmp : Program := ⸨prog|
swap_jmp:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  jmp %rcx
⸩

def SwapJmpPost (s : MachineData) (u : MachineState) : Prop :=
  u.pc = .ofBitVec s.regs.rcx.toBitVec ∧
    ∃ status, u.data = { s with
      regs := { s.regs with rax := s.regs.rbx, rbx := s.regs.rax }
      status }

theorem swapJmp_spec {l : Layout} {prog : Program} [l.WellFormed prog] (hp : swapJmp <:+: prog) :
    Spec l prog "swap_jmp" (fun _ => True) SwapJmpPost := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  refine ⟨_, label?_infix p₁ swapJmp p₂ hP (k := 0) rfl, fun s _ => ?_⟩
  apply lift_infix p₁ swapJmp p₂ hP
  sym => kstep; tactic =>
  rename_i a _ b _ c af
  let st : StatusFlags :=
    { cf := false, pf := (BitVec.setWidth 8 c).cpop_ % 2 == BitVec.zero 8
      af := af, zf := c == BitVec.zero 64, sf := c.msb, of := false }
  refine .done _ ⟨rfl, ⟨st, ?_⟩⟩
  simp only [a, b, c, st, Nat.shiftRight_zero, BitVec.ofNat_toNat]
  congr 1
  congr 2 <;> bv_decide

def clientJmp : Program := ⸨prog|
client_jmp:
  mov $41, %rax
  mov $42, %rbx
  mov $client_done, %rcx
  jmp swap_jmp
client_done:
  jmp %rdx
⸩

def ClientJmpPost (s : MachineData) (u : MachineState) : Prop :=
  u.pc = .ofBitVec s.regs.rdx.toBitVec ∧ u.data.regs.rax = 42 ∧ u.data.regs.rbx = 41

theorem clientJmp_spec {l : Layout} {prog : Program} [l.WellFormed prog]
    (hp : clientJmp <:+: prog) (hswap : Spec l prog "swap_jmp" (fun _ => True) SwapJmpPost) :
    Spec l prog "client_jmp" (fun _ => True) ClientJmpPost := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  obtain ⟨entry, hlbl, hrun⟩ := hswap
  let ef := (l.drop p₁).apply clientJmp
  refine ⟨_, label?_infix p₁ clientJmp p₂ hP (k := 0) rfl, fun s _ => ?_⟩
  refine eventually_trans _ _ _ _
    (lift_infix p₁ clientJmp p₂ hP
      (post := fun st => st.pc = ef.addrOf 4 ∧ st.data.regs.rax = 41 ∧ st.data.regs.rbx = 42 ∧
        Int64.ofBitVec st.data.regs.rcx.toBitVec = ef.addrOf 5 ∧
        st.data.regs.rdx = s.regs.rdx) ?_) ?_
  · sym => kstep 3; tactic =>
    refine .done _ ⟨rfl, rfl, rfl, ?_, rfl⟩
    dsimp only
    rw [Int64.ofBitVec_toBitVec]
  · rintro ⟨s₁, pc₁⟩ ⟨rfl, hrax, hrbx, hrcx, hrdx⟩
    dsimp only at hrax hrbx hrcx hrdx
    apply step_at_infix p₁ clientJmp p₂ hP (k := 4) rfl
    letI := Executable.labels (l.apply prog)
    simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      ConstExpr.interp, Effects.All, Effects.All_resolve_label, hlbl,
      Int64.add_sub_cancel_left]
    refine eventually_trans _ _ _ _ (hrun s₁ trivial) ?_
    rintro ⟨s₂, pc₂⟩ ⟨hpc₂, status, rfl⟩
    dsimp only at hpc₂
    rw [hpc₂, hrcx]
    apply lift_infix p₁ clientJmp p₂ hP
    sym => kstep; tactic =>
    refine .done _ ⟨?_, hrbx, hrax⟩
    dsimp only
    rw [hrdx]

def concreteLayout : Layout :=
  { start := 0x1000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

example :
    let prog := swapJmp ++ clientJmp
    Spec concreteLayout prog "swap_jmp" (fun _ => True) SwapJmpPost ∧
      Spec concreteLayout prog "client_jmp" (fun _ => True) ClientJmpPost :=
  let prog := swapJmp ++ clientJmp
  haveI : concreteLayout.WellFormed prog := by decide
  have hswap := swapJmp_spec (l := concreteLayout) (prog := prog) (by decide)
  ⟨hswap, clientJmp_spec (l := concreteLayout) (prog := prog) (by decide) hswap⟩

end Spec.Examples.JumpSwap
