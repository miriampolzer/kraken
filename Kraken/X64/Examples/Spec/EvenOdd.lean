module

import Kraken.X64.Spec
import Kraken.X64.Sep
import Kraken.Tactics
import Kraken.X64.Parser
import all Kraken.Separation

open Kraken (Layout)
open Std.ExtHashMap

namespace Spec.Examples.EvenOdd

attribute [local ksimp] Nat.shiftRight_zero BitVec.setWidth_eq BitVec.ofNat_toNat

def Slots : Nat → BitVec 64 → (DataMem → Prop) → DataMem → Prop
  | 0, _, R => R
  | n + 1, rsp, R => fun m =>
    ∃ bs : List UInt8, bs.length = 8 ∧
      (m =⋆ Eq (bs.At (rsp - 8#64)) ⋆ Slots n (rsp - 8#64) R)

private theorem slots_sep (n : Nat) (rsp : BitVec 64) (P Q : DataMem → Prop) :
    Slots n rsp P ⋆ Q = Slots n rsp (P ⋆ Q) := by
  induction n generalizing rsp with
  | zero => rfl
  | succ n ih =>
    funext m
    simp only [Slots, ← ih, ← sep_assoc]
    exact propext ⟨fun ⟨m1, m2, u, d, ⟨bs, l, h⟩, hq⟩ => ⟨bs, l, m1, m2, u, d, h, hq⟩,
      fun ⟨bs, l, m1, m2, u, d, h, hq⟩ => ⟨m1, m2, u, d, ⟨bs, l, h⟩, hq⟩⟩

def even : Program := ⸨prog|
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
⸩

def odd : Program := ⸨prog|
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
⸩

def Pre (ra : Int64) (R : DataMem → Prop) (s : MachineData) : Prop :=
  s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆
    Slots s.regs.rdi.toNat (s.regs.get64 .rsp) R

def PreLt (n : Nat) (ra : Int64) (R : DataMem → Prop) (s : MachineData) : Prop :=
  s.regs.rdi.toNat < n ∧ Pre ra R s

def Post (r : Nat) (ra : Int64) (R : DataMem → Prop) (s : MachineData) (u : MachineState) : Prop :=
  u.pc = ra ∧
    u.data.regs.rax.toNat = (s.regs.rdi.toNat + r) % 2 ∧
    u.data.regs.rsp = s.regs.rsp + 8 ∧
    Pre ra R { u.data with regs := s.regs }

theorem even_step {l : Layout} {prog : Program} [l.WellFormed prog] (hp : even <:+: prog)
    (n : Nat) (ih : ∀ ra R, Spec l prog "odd" (PreLt n ra R) (Post 0 ra R))
    (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "even" (PreLt (n + 1) ra R) (Post 1 ra R) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  let ef := (l.drop p₁).apply even
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have hra_len : raBytes.length = 8 := Int.toBytes_length 8 _
  refine ⟨_, label?_infix p₁ even p₂ hP (k := 0) rfl, fun s ⟨hlt, hmem⟩ => ?_⟩
  by_cases hrdi : s.regs.rdi = 0
  · apply lift_infix p₁ even p₂ hP
    have hrdi_nat : s.regs.rdi.toNat = 0 := by simp [hrdi]
    have hra : s.dmem =⋆ Eq (raBytes.At s.regs.rsp.toBitVec) ⋆ R := by
      rw [Pre, hrdi_nat] at hmem
      exact hmem
    sym => kstep; tactic =>
    rename_i v af
    have hv : v = BitVec.zero 64 := by simp [v, hrdi]
    simp only [hv, beq_self_eq_true, ↓reduceIte]
    sym => kstep; tactic =>
    refine .done _ ⟨?_, ?_, rfl, ?_⟩
    · dsimp only
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · dsimp only
      rw [hrdi_nat]
      decide
    · exact hmem
  · obtain ⟨k, hk⟩ : ∃ k, s.regs.rdi.toNat = k + 1 := ⟨s.regs.rdi.toNat - 1, by grind⟩
    refine eventually_trans _ _ _ _
      (lift_infix p₁ even p₂ hP
        (post := fun st => ∃ status,
          st = ⟨{ s with regs := { s.regs with rdi := s.regs.rdi - 1 }, status },
            ef.addrOf 4⟩) ?_) ?_
    · sym => kstep; tactic =>
      rename_i v af
      have hcond : (v == BitVec.zero 64) = false := by
        simp only [v, Nat.shiftRight_zero, BitVec.ofNat_toNat,
          BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne]
        grind
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      sym => kstep 1; tactic =>
      rename_i v₁ status₁
      refine .done _ ⟨status₁, ?_⟩
      simp only [v₁, Nat.shiftRight_zero, BitVec.ofNat_toNat]
      congr 3
    · rintro _ ⟨status₁, rfl⟩
      obtain ⟨bs, hbs, htop⟩ : s.dmem =⋆
          Slots (k + 1) (s.regs.get64 .rsp)
            (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp))) := by
        rw [Pre, hk, sep_comm, slots_sep] at hmem
        exact hmem
      have hrdi_sub : (s.regs.rdi - 1).toNat = k := by grind
      obtain ⟨entry_o, hlbl_o, hrun_o⟩ :=
        ih (ef.addrOf 5) (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp)))
      have hv := Mem.loadInt_sep bs _ 8 _ _ htop hbs (by decide)
      dsimp only [Reg64s.get64, Width.bytes] at hv
      apply step_at_infix p₁ even p₂ hP (k := 4) rfl
      letI := Executable.labels (l.apply prog)
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, MachineData.store, Effects.All_resolve_label, hlbl_o,
        Effects.All_require_write_access, Width.bytes, Width.bytesv, Width.bits, Reg64s.get64, hv,
        Effects.All, Int64.add_sub_cancel_left, Int64.ofBitVec_toBitVec]
      have hcall_mem :
          Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (ef.addrOf 5).toBitVec.toInt =⋆
            Eq ((Int.toBytes 8 (ef.addrOf 5).toBitVec.toInt).At (s.regs.get64 .rsp - 8#64)) ⋆
              Slots k (s.regs.get64 .rsp - 8#64)
                (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp))) :=
        Mem.storeInt_sep _ 8 bs _ s.dmem ⟨htop, hbs⟩ _
      refine eventually_trans _ _ _ _ (hrun_o _ ⟨by dsimp only [Reg64s.set64]; omega, by
        dsimp only [Pre, Reg64s.get64, Reg64s.set64, Width.bytesv, Width.bytes, Width.bits]
        exact hrdi_sub ▸ hcall_mem⟩) ?_
      rintro ⟨t1, pc1⟩ ⟨rfl, ht1_rax, ht1_rsp, ht1_pre⟩
      dsimp only [Pre, Reg64s.get64, Reg64s.set64] at ht1_rax ht1_rsp ht1_pre
      rw [hrdi_sub] at ht1_rax ht1_pre
      have ht1_rsp_eq : t1.regs.rsp = s.regs.rsp := by
        rw [ht1_rsp]
        exact UInt64.sub_add_cancel s.regs.rsp 8
      let bs5 := Int.toBytes 8 (ef.addrOf 5).toBitVec.toInt
      have hbs5 : bs5.length = 8 := Int.toBytes_length 8 _
      have ht1_slots : t1.dmem =⋆
          Slots (k + 1) (s.regs.get64 .rsp) (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp))) :=
        ⟨bs5, hbs5, ht1_pre⟩
      have ht1_ra : t1.dmem =⋆
          Eq (raBytes.At t1.regs.rsp.toBitVec) ⋆ Slots (k + 1) (s.regs.get64 .rsp) R := by
        rw [ht1_rsp_eq]
        dsimp only [Reg64s.get64] at ht1_slots ⊢
        rwa [← slots_sep, sep_comm] at ht1_slots
      apply lift_infix p₁ even p₂ hP
      sym => kstep; tactic =>
      refine .done _ ⟨?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
      · dsimp only
        omega
      · exact congrArg (· + 8) ht1_rsp_eq
      · dsimp only [Pre]
        rw [hk]
        simpa only [Reg64s.get64, ht1_rsp_eq] using ht1_ra

theorem odd_step {l : Layout} {prog : Program} [l.WellFormed prog] (hp : odd <:+: prog)
    (n : Nat) (ih : ∀ ra R, Spec l prog "even" (PreLt n ra R) (Post 1 ra R))
    (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "odd" (PreLt (n + 1) ra R) (Post 0 ra R) := by
  obtain ⟨p₁, p₂, hP⟩ := hp
  let ef := (l.drop p₁).apply odd
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have hra_len : raBytes.length = 8 := Int.toBytes_length 8 _
  refine ⟨_, label?_infix p₁ odd p₂ hP (k := 0) rfl, fun s ⟨hlt, hmem⟩ => ?_⟩
  by_cases hrdi : s.regs.rdi = 0
  · apply lift_infix p₁ odd p₂ hP
    have hrdi_nat : s.regs.rdi.toNat = 0 := by simp [hrdi]
    have hra : s.dmem =⋆ Eq (raBytes.At s.regs.rsp.toBitVec) ⋆ R := by
      rw [Pre, hrdi_nat] at hmem
      exact hmem
    sym => kstep; tactic =>
    rename_i v af
    have hv : v = BitVec.zero 64 := by simp [v, hrdi]
    simp only [hv, beq_self_eq_true, ↓reduceIte]
    sym => kstep; tactic =>
    refine .done _ ⟨?_, ?_, rfl, ?_⟩
    · dsimp only
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · dsimp only
      rw [hrdi_nat]
      decide
    · exact hmem
  · obtain ⟨k, hk⟩ : ∃ k, s.regs.rdi.toNat = k + 1 := ⟨s.regs.rdi.toNat - 1, by grind⟩
    refine eventually_trans _ _ _ _
      (lift_infix p₁ odd p₂ hP
        (post := fun st => ∃ status,
          st = ⟨{ s with regs := { s.regs with rdi := s.regs.rdi - 1 }, status },
            ef.addrOf 4⟩) ?_) ?_
    · sym => kstep; tactic =>
      rename_i v af
      have hcond : (v == BitVec.zero 64) = false := by
        simp only [v, Nat.shiftRight_zero, BitVec.ofNat_toNat,
          BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne]
        grind
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      sym => kstep 1; tactic =>
      rename_i v₁ status₁
      refine .done _ ⟨status₁, ?_⟩
      simp only [v₁, Nat.shiftRight_zero, BitVec.ofNat_toNat]
      congr 3
    · rintro _ ⟨status₁, rfl⟩
      obtain ⟨bs, hbs, htop⟩ : s.dmem =⋆
          Slots (k + 1) (s.regs.get64 .rsp)
            (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp))) := by
        rw [Pre, hk, sep_comm, slots_sep] at hmem
        exact hmem
      have hrdi_sub : (s.regs.rdi - 1).toNat = k := by grind
      obtain ⟨entry_e, hlbl_e, hrun_e⟩ :=
        ih (ef.addrOf 5) (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp)))
      have hv := Mem.loadInt_sep bs _ 8 _ _ htop hbs (by decide)
      dsimp only [Reg64s.get64, Width.bytes] at hv
      apply step_at_infix p₁ odd p₂ hP (k := 4) rfl
      letI := Executable.labels (l.apply prog)
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, MachineData.store, Effects.All_resolve_label, hlbl_e,
        Effects.All_require_write_access, Width.bytes, Width.bytesv, Width.bits, Reg64s.get64, hv,
        Effects.All, Int64.add_sub_cancel_left, Int64.ofBitVec_toBitVec]
      have hcall_mem :
          Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (ef.addrOf 5).toBitVec.toInt =⋆
            Eq ((Int.toBytes 8 (ef.addrOf 5).toBitVec.toInt).At (s.regs.get64 .rsp - 8#64)) ⋆
              Slots k (s.regs.get64 .rsp - 8#64)
                (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp))) :=
        Mem.storeInt_sep _ 8 bs _ s.dmem ⟨htop, hbs⟩ _
      refine eventually_trans _ _ _ _ (hrun_e _ ⟨by dsimp only [Reg64s.set64]; omega, by
        dsimp only [Pre, Reg64s.get64, Reg64s.set64, Width.bytesv, Width.bytes, Width.bits]
        exact hrdi_sub ▸ hcall_mem⟩) ?_
      rintro ⟨t1, pc1⟩ ⟨rfl, ht1_rax, ht1_rsp, ht1_pre⟩
      dsimp only [Pre, Reg64s.get64, Reg64s.set64] at ht1_rax ht1_rsp ht1_pre
      rw [hrdi_sub] at ht1_rax ht1_pre
      have ht1_rsp_eq : t1.regs.rsp = s.regs.rsp := by
        rw [ht1_rsp]
        exact UInt64.sub_add_cancel s.regs.rsp 8
      let bs5 := Int.toBytes 8 (ef.addrOf 5).toBitVec.toInt
      have hbs5 : bs5.length = 8 := Int.toBytes_length 8 _
      have ht1_slots : t1.dmem =⋆
          Slots (k + 1) (s.regs.get64 .rsp) (R ⋆ Eq (raBytes.At (s.regs.get64 .rsp))) :=
        ⟨bs5, hbs5, ht1_pre⟩
      have ht1_ra : t1.dmem =⋆
          Eq (raBytes.At t1.regs.rsp.toBitVec) ⋆ Slots (k + 1) (s.regs.get64 .rsp) R := by
        rw [ht1_rsp_eq]
        dsimp only [Reg64s.get64] at ht1_slots ⊢
        rwa [← slots_sep, sep_comm] at ht1_slots
      apply lift_infix p₁ odd p₂ hP
      sym => kstep; tactic =>
      refine .done _ ⟨?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
      · dsimp only
        omega
      · exact congrArg (· + 8) ht1_rsp_eq
      · dsimp only [Pre]
        rw [hk]
        simpa only [Reg64s.get64, ht1_rsp_eq] using ht1_ra

private theorem even_odd_lt {l : Layout} {prog : Program} [l.WellFormed prog]
    (he : even <:+: prog) (ho : odd <:+: prog) (n : Nat) :
    (∀ ra R, Spec l prog "even" (PreLt n ra R) (Post 1 ra R)) ∧
      (∀ ra R, Spec l prog "odd" (PreLt n ra R) (Post 0 ra R)) := by
  induction n with
  | zero =>
    obtain ⟨pe₁, pe₂, hPe⟩ := he
    obtain ⟨po₁, po₂, hPo⟩ := ho
    exact ⟨fun _ _ => ⟨_, label?_infix pe₁ even pe₂ hPe (k := 0) rfl, fun _ ⟨h, _⟩ => by omega⟩,
      fun _ _ => ⟨_, label?_infix po₁ odd po₂ hPo (k := 0) rfl, fun _ ⟨h, _⟩ => by omega⟩⟩
  | succ n ih => exact ⟨even_step he n ih.2, odd_step ho n ih.1⟩

theorem even_spec {l : Layout} {prog : Program} [l.WellFormed prog]
    (he : even <:+: prog) (ho : odd <:+: prog) (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "even" (Pre ra R) (Post 1 ra R) := by
  obtain ⟨entry, hlbl, _⟩ := (even_odd_lt (l := l) he ho 0).1 ra R
  refine ⟨entry, hlbl, fun s hs => ?_⟩
  obtain ⟨_, hlbl', hrun⟩ := (even_odd_lt (l := l) he ho (s.regs.rdi.toNat + 1)).1 ra R
  cases hlbl.symm.trans hlbl'
  exact hrun s ⟨Nat.lt_succ_self _, hs⟩

theorem odd_spec {l : Layout} {prog : Program} [l.WellFormed prog]
    (he : even <:+: prog) (ho : odd <:+: prog) (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "odd" (Pre ra R) (Post 0 ra R) := by
  obtain ⟨entry, hlbl, _⟩ := (even_odd_lt (l := l) he ho 0).2 ra R
  refine ⟨entry, hlbl, fun s hs => ?_⟩
  obtain ⟨_, hlbl', hrun⟩ := (even_odd_lt (l := l) he ho (s.regs.rdi.toNat + 1)).2 ra R
  cases hlbl.symm.trans hlbl'
  exact hrun s ⟨Nat.lt_succ_self _, hs⟩

def concreteLayout : Layout :=
  { start := 0x1000, instrSize := fun _ => 4, instrSize_pos := fun _ => by decide }

example (ra : Int64) (R : DataMem → Prop) :
    let prog := even ++ odd
    Spec concreteLayout prog "even" (Pre ra R) (Post 1 ra R) ∧
      Spec concreteLayout prog "odd" (Pre ra R) (Post 0 ra R) :=
  let prog := even ++ odd
  haveI : concreteLayout.WellFormed prog := by decide
  ⟨even_spec (l := concreteLayout) (prog := prog) (by decide) (by decide) ra R,
   odd_spec (l := concreteLayout) (prog := prog) (by decide) (by decide) ra R⟩

end Spec.Examples.EvenOdd
