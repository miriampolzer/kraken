module

import Kraken.X64.Spec
import Kraken.X64.Sep
import Kraken.Tactics
import Kraken.X64.Parser

open Kraken (Layout)
open Std.ExtHashMap

namespace Spec.Examples.Tightness

attribute [local ksimp] Nat.shiftRight_zero BitVec.setWidth_eq BitVec.ofNat_toNat

def seven : Program := ⸨prog|
seven:
  mov $7, %rax
  ret
⸩

def RetPre (ra : Int64) (R : DataMem → Prop) (s : MachineData) : Prop :=
  s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R

theorem seven_spec {l : Layout} {prog : Program} [l.WellFormed prog] (hp : seven <:+: prog)
    (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "seven" (RetPre ra R) (fun _ u => u.pc = ra ∧ u.data.regs.rax = 7) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  refine ⟨_, label?_infix p₁ seven p₂ hP (k := 0) rfl, fun s hmem => ?_⟩
  apply lift_infix p₁ seven p₂ hP
  dsimp only [RetPre, Reg64s.get64] at hmem
  have hra_len : (Int.toBytes 8 ra.toBitVec.toInt).length = 8 := Int.toBytes_length 8 _
  sym => kstep; tactic =>
  refine .done _ ⟨?_, rfl⟩
  dsimp only
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

theorem not_seven_spec_eight {l : Layout} {prog : Program} [l.WellFormed prog]
    (hsz : (l.apply prog).size < 2 ^ 64 - 1) (hp : seven <:+: prog)
    (R : DataMem → Prop) (s : MachineData) (hs : RetPre (l.start - 1) R s) :
    ¬ Spec l prog "seven" (RetPre (l.start - 1) R)
      (fun _ u => u.pc = l.start - 1 ∧ u.data.regs.rax = 8) := by
  intro h8
  have hst := stalls_sub_one hsz
  have hboth := (seven_spec hp (l.start - 1) R).and h8 fun _ _ _ h => by
    rcases h with ⟨hpc, _⟩ | ⟨hpc, _⟩ <;> exact hpc ▸ hst
  obtain ⟨_, _, hrun⟩ := hboth
  obtain ⟨_, ⟨_, h7⟩, _, h8'⟩ := (hrun s hs).exists
  exact absurd (h7.symm.trans h8') (by decide)

def concreteLayout : Layout :=
  { start := 0x1000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

example :
    ¬ Spec concreteLayout seven "seven" (RetPre (concreteLayout.start - 1) emp)
      (fun _ u => u.pc = concreteLayout.start - 1 ∧ u.data.regs.rax = 8) := by
  haveI : concreteLayout.WellFormed seven := by decide
  let ra := concreteLayout.start - 1
  let s : MachineData :=
    { regs := ({} : Reg64s).set64 .rsp 0x8000#64
      dmem := (Int.toBytes 8 ra.toBitVec.toInt).At 0x8000#64 }
  exact not_seven_spec_eight (by decide) (by decide) emp s
    (by unfold RetPre; exact (sep_emp (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At _))).symm ▸ rfl)

end Spec.Examples.Tightness
