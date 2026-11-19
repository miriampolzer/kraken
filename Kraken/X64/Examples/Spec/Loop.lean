module

import Kraken.X64.Spec
import Kraken.X64.Sep
import Kraken.Tactics
import Kraken.X64.Parser

open Kraken (Layout)

namespace Spec.Examples.Loop

attribute [local ksimp] Nat.shiftRight_zero BitVec.setWidth_eq BitVec.ofNat_toNat

def countdown : Program := ⸨prog|
countdown:
  test %rdi, %rdi
  jz countdown_done
  dec %rdi
  jmp countdown
countdown_done:
  ret
⸩

def CountdownPre (ra : Int64) (R : DataMem → Prop) (s : MachineData) : Prop :=
  s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R

def CountdownPost (ra : Int64) (R : DataMem → Prop) (s : MachineData) (u : MachineState) : Prop :=
  u.pc = ra ∧ u.data.regs.rdi = 0 ∧ u.data.regs.rsp = s.regs.rsp + 8 ∧
    CountdownPre ra R { u.data with regs := s.regs }

theorem countdown_spec {l : Layout} {prog : Program} [l.WellFormed prog]
    (hp : countdown <:+: prog) (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "countdown" (CountdownPre ra R) (CountdownPost ra R) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have hra_len : raBytes.length = 8 := Int.toBytes_length 8 _
  refine ⟨_, label?_infix p₁ countdown p₂ hP (k := 0) rfl, fun s hmem => ?_⟩
  apply lift_infix p₁ countdown p₂ hP
  intro
  have hloop (n : Nat) : ∀ (st : MachineData),
      st.regs.rdi.toNat = n → st.regs.rsp = s.regs.rsp →
      (st.dmem =⋆ Eq (raBytes.At s.regs.rsp.toBitVec) ⋆ R) →
      Eventually (step1 ((l.drop p₁).apply countdown))
        (CountdownPost ra R s) ⟨st, ((l.drop p₁).apply countdown).addrOf 0⟩ := by
    induction n with
    | zero =>
      intro st hst hrsp hm
      have hrdi : st.regs.rdi = 0 := by grind
      have hm' : st.dmem =⋆ Eq (raBytes.At st.regs.rsp.toBitVec) ⋆ R := by rwa [hrsp]
      sym => kstep; tactic =>
      rename_i v af
      have hv : v = BitVec.zero 64 := by simp [v, hrdi]
      simp only [hv, beq_self_eq_true, ↓reduceIte]
      sym => kstep; tactic =>
      refine .done _ ⟨?_, hrdi, congrArg (· + 8) hrsp, hm⟩
      dsimp only
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    | succ k ih =>
      intro st hst hrsp hm
      sym => kstep; tactic =>
      rename_i v af
      have hcond : (v == BitVec.zero 64) = false := by
        simp only [v, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne]
        grind
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      sym => kstep 2; tactic =>
      apply ih
      · dsimp +zetaDelta only
        grind
      · exact hrsp
      · exact hm
  exact hloop s.regs.rdi.toNat s rfl rfl hmem

def concreteLayout : Layout :=
  { start := 0x1000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

example (ra : Int64) (R : DataMem → Prop) :
    Spec concreteLayout countdown "countdown" (CountdownPre ra R) (CountdownPost ra R) :=
  haveI : concreteLayout.WellFormed countdown := by decide
  countdown_spec (by decide) ra R

end Spec.Examples.Loop
