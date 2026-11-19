module

import Kraken.X64.Spec
import Kraken.X64.Sep
import Kraken.Tactics
import Kraken.X64.Parser

open Kraken (Layout)
open Std.ExtHashMap

namespace Spec.Examples.CallSwap

attribute [local ksimp] Nat.shiftRight_zero BitVec.setWidth_eq BitVec.ofNat_toNat

def swap : Program := ⸨prog|
swap:
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax
  ret
⸩

def SwapPre (ra : Int64) (R : DataMem → Prop) (s : MachineData) : Prop :=
  s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆ R

def SwapPost (ra : Int64) (R : DataMem → Prop) (s : MachineData) (u : MachineState) : Prop :=
  u.pc = ra ∧
    (∃ status, u.data = { s with
      regs := { s.regs with rax := s.regs.rbx, rbx := s.regs.rax, rsp := s.regs.rsp + 8 }
      status }) ∧
    SwapPre ra R { u.data with regs := s.regs }

theorem swap_spec {l : Layout} {prog : Program} [l.WellFormed prog] (hp : swap <:+: prog)
    (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "swap" (SwapPre ra R) (SwapPost ra R) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  have hra_len : (Int.toBytes 8 ra.toBitVec.toInt).length = 8 := Int.toBytes_length 8 _
  refine ⟨_, label?_infix p₁ swap p₂ hP (k := 0) rfl, fun s hmem => ?_⟩
  apply lift_infix p₁ swap p₂ hP
  dsimp only [SwapPre, Reg64s.get64] at hmem
  sym => kstep; tactic =>
  rename_i a _ b _ c af _
  let st : StatusFlags :=
    { cf := false, pf := (BitVec.setWidth 8 c).cpop_ % 2 == BitVec.zero 8
      af := af, zf := c == BitVec.zero 64, sf := c.msb, of := false }
  refine .done _ ⟨?_, ⟨st, ?_⟩, hmem⟩
  · dsimp only
    rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · simp only [a, b, c, st, Nat.shiftRight_zero, BitVec.ofNat_toNat]
    congr 1
    congr 2 <;> bv_decide

def pswap : Program := ⸨prog|
pswap:
  call swap
  call swap
  ret
⸩

def PswapPre (ra : Int64) (R : DataMem → Prop) (s : MachineData) : Prop :=
  ∃ bs : List UInt8, bs.length = 8 ∧
    (s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆
      Eq (bs.At (s.regs.get64 .rsp - 8#64)) ⋆ R)

def PswapPost (ra : Int64) (R : DataMem → Prop) (s : MachineData) (u : MachineState) : Prop :=
  u.pc = ra ∧
    (∃ status, u.data = { s with
      regs := { s.regs with rsp := s.regs.rsp + 8 }
      status
      dmem := u.data.dmem }) ∧
    PswapPre ra R { u.data with regs := s.regs }

theorem pswap_spec {l : Layout} {prog : Program} [l.WellFormed prog] (hp : pswap <:+: prog)
    (hswap : ∀ ra R, Spec l prog "swap" (SwapPre ra R) (SwapPost ra R))
    (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "pswap" (PswapPre ra R) (PswapPost ra R) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  let ef := (l.drop p₁).apply pswap
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have hra_len : raBytes.length = 8 := Int.toBytes_length 8 _
  have haddr0 : ef.addrOf 0 = ef.addrOf 1 :=
    ((ef.addrOf_succ (n := 0) rfl).trans (Int64.add_zero _)).symm
  refine ⟨_, label?_infix p₁ pswap p₂ hP (k := 0) rfl, fun s ⟨bs, hbs, hmem⟩ => ?_⟩
  rw [haddr0]
  have hmem_slot : s.dmem =⋆
      Eq (bs.At (s.regs.get64 .rsp - 8#64)) ⋆ (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R) := by
    rw [sep_assoc] at hmem
    rwa [sep_comm_l] at hmem
  obtain ⟨entry₁, hlbl₁, hrun₁⟩ := hswap (ef.addrOf 2) (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R)
  have hv₁ := Mem.loadInt_sep bs _ 8 _ _ hmem_slot hbs (by decide)
  apply step_at_infix p₁ pswap p₂ hP (k := 1) rfl
  letI := Executable.labels (l.apply prog)
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Effects.All_resolve_label, hlbl₁,
    Effects.All_require_write_access, Width.bytes, Width.bytesv, Width.bits, hv₁, Effects.All,
    Int64.add_sub_cancel_left, Int64.ofBitVec_toBitVec]
  have hc1_pre :
      Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (ef.addrOf 2).toBitVec.toInt =⋆
        Eq ((Int.toBytes 8 (ef.addrOf 2).toBitVec.toInt).At (s.regs.get64 .rsp - 8#64)) ⋆
          (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R) :=
    Mem.storeInt_sep _ 8 bs _ s.dmem ⟨hmem_slot, hbs⟩ _
  refine eventually_trans _ _ _ _ (hrun₁ _ hc1_pre) ?_
  rintro ⟨t1, pc1⟩ ⟨rfl, ⟨st1, rfl⟩, ht1_mem⟩
  dsimp only [SwapPre, Reg64s.get64, Reg64s.set64] at ht1_mem
  have ht1_rsp : ({ toBitVec := s.regs.rsp.toBitVec - 8#64 } : UInt64) + 8 = s.regs.rsp :=
    UInt64.sub_add_cancel s.regs.rsp 8
  let bs2 := Int.toBytes 8 (ef.addrOf 2).toBitVec.toInt
  have hbs2 : bs2.length = 8 := Int.toBytes_length 8 _
  obtain ⟨entry₂, hlbl₂, hrun₂⟩ := hswap (ef.addrOf 3) (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R)
  have hv₂ := Mem.loadInt_sep bs2 _ 8 _ _ ht1_mem hbs2 (by decide)
  apply step_at_infix p₁ pswap p₂ hP (k := 2) rfl
  dsimp +zetaDelta only [Reg64s.get64, Reg64s.set64, Width.bytes] at hv₂ ⊢
  rw [ht1_rsp]
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Effects.All_resolve_label, hlbl₂,
    Effects.All_require_write_access, Width.bytes, Width.bytesv, Width.bits, Reg64s.get64,
    hv₂, Effects.All, Int64.add_sub_cancel_left, Int64.ofBitVec_toBitVec]
  have hc2_pre :
      Mem.storeInt (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 (ef.addrOf 2).toBitVec.toInt)
        (s.regs.rsp.toBitVec - 8#64) 8 (ef.addrOf 3).toBitVec.toInt =⋆
          Eq ((Int.toBytes 8 (ef.addrOf 3).toBitVec.toInt).At (s.regs.rsp.toBitVec - 8#64)) ⋆
            (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R) :=
    Mem.storeInt_sep _ 8 bs2 _ _ ⟨ht1_mem, hbs2⟩ _
  refine eventually_trans _ _ _ _ (hrun₂ _ (by
    simpa only [SwapPre, Reg64s.get64, Reg64s.set64] using hc2_pre)) ?_
  rintro ⟨t2, pc2⟩ ⟨rfl, ⟨st2, rfl⟩, ht2_mem⟩
  dsimp only [SwapPre, Reg64s.get64, Reg64s.set64] at ht2_mem
  let bs3 := Int.toBytes 8 (ef.addrOf 3).toBitVec.toInt
  have hbs3 : bs3.length = 8 := Int.toBytes_length 8 _
  have ht2_ra :
      Mem.storeInt (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 (ef.addrOf 2).toBitVec.toInt)
        (s.regs.rsp.toBitVec - 8#64) 8 (ef.addrOf 3).toBitVec.toInt =⋆
          Eq (raBytes.At (({ toBitVec := s.regs.rsp.toBitVec - 8#64 } : UInt64) + 8).toBitVec) ⋆
            (Eq (bs3.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) := by
    rw [ht1_rsp]
    rwa [sep_comm_l] at ht2_mem
  apply lift_infix p₁ pswap p₂ hP
  sym => kstep; tactic =>
  refine .done _ ⟨?_, ⟨st2, ?_⟩, bs3, hbs3, ?_⟩
  · dsimp only
    rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · dsimp +zetaDelta only [Reg64s.get64, Reg64s.set64]
    rw [ht1_rsp]
    rcases s with ⟨⟨⟩, _, _, _, _⟩
    rfl
  · dsimp only [Reg64s.get64] at ht2_ra ⊢
    rw [ht1_rsp] at ht2_ra
    rwa [← sep_assoc] at ht2_ra

def tailPswap : Program := ⸨prog|
tail_pswap:
  call swap
  jmp swap
⸩

theorem tailPswap_spec {l : Layout} {prog : Program} [l.WellFormed prog] (hp : tailPswap <:+: prog)
    (hswap : ∀ ra R, Spec l prog "swap" (SwapPre ra R) (SwapPost ra R))
    (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "tail_pswap" (PswapPre ra R) (PswapPost ra R) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  let ef := (l.drop p₁).apply tailPswap
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have haddr0 : ef.addrOf 0 = ef.addrOf 1 :=
    ((ef.addrOf_succ (n := 0) rfl).trans (Int64.add_zero _)).symm
  refine ⟨_, label?_infix p₁ tailPswap p₂ hP (k := 0) rfl, fun s ⟨bs, hbs, hmem⟩ => ?_⟩
  rw [haddr0]
  have hmem_slot : s.dmem =⋆
      Eq (bs.At (s.regs.get64 .rsp - 8#64)) ⋆ (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R) := by
    rw [sep_assoc] at hmem
    rwa [sep_comm_l] at hmem
  obtain ⟨entry₁, hlbl₁, hrun₁⟩ := hswap (ef.addrOf 2) (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R)
  have hv₁ := Mem.loadInt_sep bs _ 8 _ _ hmem_slot hbs (by decide)
  apply step_at_infix p₁ tailPswap p₂ hP (k := 1) rfl
  letI := Executable.labels (l.apply prog)
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Effects.All_resolve_label, hlbl₁,
    Effects.All_require_write_access, Width.bytes, Width.bytesv, Width.bits, hv₁, Effects.All,
    Int64.add_sub_cancel_left, Int64.ofBitVec_toBitVec]
  have hc1_pre :
      Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (ef.addrOf 2).toBitVec.toInt =⋆
        Eq ((Int.toBytes 8 (ef.addrOf 2).toBitVec.toInt).At (s.regs.get64 .rsp - 8#64)) ⋆
          (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R) :=
    Mem.storeInt_sep _ 8 bs _ s.dmem ⟨hmem_slot, hbs⟩ _
  refine eventually_trans _ _ _ _ (hrun₁ _ hc1_pre) ?_
  rintro ⟨t1, pc1⟩ ⟨rfl, ⟨st1, rfl⟩, ht1_mem⟩
  dsimp only [SwapPre, Reg64s.get64, Reg64s.set64] at ht1_mem
  have ht1_rsp : ({ toBitVec := s.regs.rsp.toBitVec - 8#64 } : UInt64) + 8 = s.regs.rsp :=
    UInt64.sub_add_cancel s.regs.rsp 8
  let bs2 := Int.toBytes 8 (ef.addrOf 2).toBitVec.toInt
  have hbs2 : bs2.length = 8 := Int.toBytes_length 8 _
  have ht1_ra :
      Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (ef.addrOf 2).toBitVec.toInt =⋆
        Eq (raBytes.At (({ toBitVec := s.regs.rsp.toBitVec - 8#64 } : UInt64) + 8).toBitVec) ⋆
          (Eq (bs2.At (s.regs.get64 .rsp - 8#64)) ⋆ R) := by
    rw [ht1_rsp]
    rwa [sep_comm_l] at ht1_mem
  obtain ⟨entry₂, hlbl₂, hrun₂⟩ := hswap ra (Eq (bs2.At (s.regs.get64 .rsp - 8#64)) ⋆ R)
  apply step_at_infix p₁ tailPswap p₂ hP (k := 2) rfl
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All_resolve_label, hlbl₂, Effects.All, Int64.add_sub_cancel_left]
  refine eventually_weaken _ _ _ _ ?_ (hrun₂ _ (by
    simpa only [SwapPre, Reg64s.get64, Reg64s.set64] using ht1_ra))
  rintro ⟨t2, pc2⟩ ⟨hpc2, ⟨st2, rfl⟩, ht2_mem⟩
  refine ⟨hpc2, ⟨st2, ?_⟩, bs2, hbs2, ?_⟩
  · dsimp +zetaDelta only [Reg64s.get64, Reg64s.set64]
    rw [ht1_rsp]
  · dsimp only [SwapPre, Reg64s.get64, Reg64s.set64] at ht2_mem ⊢
    rw [ht1_rsp] at ht2_mem
    rwa [← sep_assoc] at ht2_mem

def concreteLayout : Layout :=
  { start := 0x1000, instrSize := fun _ => 5, instrSize_pos := fun _ => by decide }

example (ra : Int64) (R : DataMem → Prop) :
    let prog := swap ++ pswap ++ tailPswap
    Spec concreteLayout prog "swap" (SwapPre ra R) (SwapPost ra R) ∧
      Spec concreteLayout prog "pswap" (PswapPre ra R) (PswapPost ra R) ∧
      Spec concreteLayout prog "tail_pswap" (PswapPre ra R) (PswapPost ra R) :=
  let prog := swap ++ pswap ++ tailPswap
  haveI : concreteLayout.WellFormed prog := by decide
  have hswap := fun ra' R' => swap_spec (l := concreteLayout) (prog := prog) (by decide) ra' R'
  ⟨hswap ra R,
   pswap_spec (l := concreteLayout) (prog := prog) (by decide) hswap ra R,
   tailPswap_spec (l := concreteLayout) (prog := prog) (by decide) hswap ra R⟩

end Spec.Examples.CallSwap
