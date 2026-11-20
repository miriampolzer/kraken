module

import Kraken.X64.Spec
import Kraken.X64.Sep
import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.SeparationTactics

open Kraken (Layout)
open Std.ExtHashMap

namespace Spec.Examples.Memcpy

attribute [local ksimp]
  Int.add_zero
  Int64.toInt_zero
  BitVec.ofInt_toInt
  BitVec.add_zero
  Nat.shiftRight_zero
  BitVec.setWidth_eq
  BitVec.ofNat_toNat

def memcpy : Program := ⸨prog|
memcpy:
  mov %rdi, %rax
memcpy_qword:
  cmp $8, %rdx
  jb memcpy_byte
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  add $8, %rsi
  add $8, %rdi
  sub $8, %rdx
  jmp memcpy_qword
memcpy_byte:
  test %rdx, %rdx
  jz memcpy_done
  movb (%rsi), %cl
  movb %cl, (%rdi)
  inc %rsi
  inc %rdi
  dec %rdx
  jmp memcpy_byte
memcpy_done:
  ret
⸩

def MemcpyPre (dstBytes srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop)
    (s : MachineData) : Prop :=
  dstBytes.length = s.regs.rdx.toNat ∧
    srcBytes.length = s.regs.rdx.toNat ∧
    (s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆
      Eq (dstBytes.At (s.regs.get64 .rdi)) ⋆
      Eq (srcBytes.At (s.regs.get64 .rsi)) ⋆ R)

def MemcpyPost (srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop)
    (s : MachineData) (u : MachineState) : Prop :=
  u.pc = ra ∧
    (∃ rcx status, u.data = { s with
      regs := { s.regs with
        rax := s.regs.rdi
        rcx := rcx
        rdx := 0
        rsi := s.regs.rsi + s.regs.rdx
        rdi := s.regs.rdi + s.regs.rdx
        rsp := s.regs.rsp + 8 }
      status
      dmem := u.data.dmem }) ∧
    (u.data.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆
      Eq (srcBytes.At (s.regs.get64 .rdi)) ⋆
      Eq (srcBytes.At (s.regs.get64 .rsi)) ⋆ R)

private structure LoopGhost where
  dst : UInt64
  src : UInt64
  dstBytes : List UInt8
  srcBytes : List UInt8
  frame : DataMem → Prop

private def LoopInv (pc : Int64) (s₀ : MachineData) (g : LoopGhost)
    (st : MachineState) : Prop :=
  st.pc = pc ∧
    g.dstBytes.length = g.srcBytes.length ∧
    st.data.regs.rdx.toNat = g.srcBytes.length ∧
    (∃ rcx status, st.data = { s₀ with
      regs := { s₀.regs with
        rax := s₀.regs.rdi
        rcx := rcx
        rdx := st.data.regs.rdx
        rsi := g.src
        rdi := g.dst }
      status
      dmem := st.data.dmem }) ∧
    (st.data.dmem =⋆ Eq (g.dstBytes.At g.dst.toBitVec) ⋆
      (Eq (g.srcBytes.At g.src.toBitVec) ⋆ g.frame))

private def DonePost (pc : Int64) (s₀ : MachineData) (g : LoopGhost)
    (u : MachineState) : Prop :=
  u.pc = pc ∧
    (∃ rcx status, u.data = { s₀ with
      regs := { s₀.regs with
        rax := s₀.regs.rdi
        rcx := rcx
        rdx := 0
        rsi := g.src + .ofNat g.srcBytes.length
        rdi := g.dst + .ofNat g.srcBytes.length }
      status
      dmem := u.data.dmem }) ∧
    (u.data.dmem =⋆ Eq (g.srcBytes.At g.dst.toBitVec) ⋆
      (Eq (g.srcBytes.At g.src.toBitVec) ⋆ g.frame))

private theorem cf_sub_eq {w : Nat} (x y : BitVec w) :
    ((x - y).unsigned != x.unsigned - y.unsigned) = decide (x.toNat < y.toNat) := by
  simp only [BitVec.unsigned]
  by_cases h : x.toNat < y.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    omega
  · rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
    simp only [h, decide_false, bne_eq_false_iff_eq]
    omega

private theorem at_take_drop_sep (bs : List UInt8) (k : Nat) (a : BitVec 64)
    (hk : k ≤ bs.length) (hbound : bs.length ≤ 2 ^ 64) :
    Eq (bs.At a) =
      Eq ((bs.take k).At a) ⋆ Eq ((bs.drop k).At (a + BitVec.ofNat 64 k)) := by
  have hb : (bs.take k).length + (bs.drop k).length ≤ 2 ^ 64 := by
    rwa [← List.length_append, List.take_append_drop]
  conv =>
    lhs
    rw [← List.take_append_drop k bs]
  rw [Mem.At_append_sep _ _ _ hb, List.length_take_of_le hk]

private theorem split_loop_mem {g : LoopGhost} {k : Nat} {m : DataMem}
    (hk : k ≤ g.srcBytes.length) (hbound : g.srcBytes.length ≤ 2 ^ 64)
    (hdl : g.dstBytes.length = g.srcBytes.length)
    (hmem : m =⋆ Eq (g.dstBytes.At g.dst.toBitVec) ⋆
      (Eq (g.srcBytes.At g.src.toBitVec) ⋆ g.frame)) :
    (m =⋆ Eq ((g.srcBytes.take k).At g.src.toBitVec) ⋆
      (Eq ((g.dstBytes.take k).At g.dst.toBitVec) ⋆
        Eq ((g.dstBytes.drop k).At (g.dst.toBitVec + BitVec.ofNat 64 k)) ⋆
        Eq ((g.srcBytes.drop k).At (g.src.toBitVec + BitVec.ofNat 64 k)) ⋆ g.frame)) ∧
    (m =⋆ Eq ((g.dstBytes.take k).At g.dst.toBitVec) ⋆
      ((Eq ((g.dstBytes.drop k).At (g.dst.toBitVec + BitVec.ofNat 64 k)) ⋆
          Eq ((g.srcBytes.drop k).At (g.src.toBitVec + BitVec.ofNat 64 k))) ⋆
        (Eq ((g.srcBytes.take k).At g.src.toBitVec) ⋆ g.frame))) := by
  rw [at_take_drop_sep g.dstBytes k _ (by omega) (by omega),
    at_take_drop_sep g.srcBytes k _ hk hbound] at hmem
  exact ⟨by ecancel, by ecancel⟩

private theorem donePost_of_take_drop (pc : Int64) (s₀ : MachineData) {g : LoopGhost} {k : Nat}
    (hk : k ≤ g.srcBytes.length) (hbound : g.srcBytes.length ≤ 2 ^ 64) {u : MachineState}
    (hu : DonePost pc s₀
      ⟨g.dst + .ofNat k, g.src + .ofNat k, g.dstBytes.drop k, g.srcBytes.drop k,
        Eq ((g.srcBytes.take k).At g.dst.toBitVec) ⋆
          (Eq ((g.srcBytes.take k).At g.src.toBitVec) ⋆ g.frame)⟩ u) :
    DonePost pc s₀ g u := by
  obtain ⟨hpc, ⟨rcx, st, hdata⟩, hmem⟩ := hu
  refine ⟨hpc, ⟨rcx, st, ?_⟩, ?_⟩
  · dsimp only at hdata ⊢
    simpa only [List.length_drop, UInt64.add_assoc, ← UInt64.ofNat_add,
      Nat.add_sub_of_le hk] using hdata
  · dsimp only [UInt64.ofNat] at hmem ⊢
    rw [UInt64.toBitVec_add, UInt64.toBitVec_add] at hmem
    rw [at_take_drop_sep g.srcBytes k g.dst.toBitVec hk hbound,
      at_take_drop_sep g.srcBytes k g.src.toBitVec hk hbound]
    ecancel

private theorem memcpy_byte_loop {l : Layout} [l.WellFormed memcpy] (s₀ : MachineData)
    (g₀ : LoopGhost) (st₀ : MachineState)
    (h₀ : LoopInv ((l.apply memcpy).addrOf 11) s₀ g₀ st₀) :
    Eventually (step1 (l.apply memcpy))
      (DonePost ((l.apply memcpy).addrOf 20) s₀ g₀) st₀ := by
  refine tailrec_loop
    (InvImage.wf (r := (· < ·)) (fun g : LoopGhost => g.srcBytes.length) Nat.lt_wfRel.wf)
    (fun g ⟨s, pc⟩ hinv => ?_) g₀ h₀
  obtain ⟨rfl, hdl, hrdx, ⟨rcx, status, hs_eq⟩, hmem⟩ := hinv
  dsimp only at hdl hrdx hs_eq hmem
  have hrsi : s.regs.rsi = g.src := by rw [congrArg MachineData.regs hs_eq]
  have hrdi : s.regs.rdi = g.dst := by rw [congrArg MachineData.regs hs_eq]
  by_cases hv0 : g.srcBytes.length = 0
  · have hd_nil : g.dstBytes = [] := List.eq_nil_of_length_eq_zero (hdl.trans hv0)
    have hs_nil : g.srcBytes = [] := List.eq_nil_of_length_eq_zero hv0
    have hrdx0 : s.regs.rdx = 0 := by grind
    sym => kstep; tactic =>
    rename_i w af
    have hw : w = BitVec.zero 64 := by simp [w, hrdx0]
    simp only [hw, beq_self_eq_true, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine .done _ (.inl ⟨rfl, ?_, ?_⟩)
    · dsimp +zetaDelta only [UInt64.ofNat]
      exact ⟨rcx, _, by
        rw [show s = _ from hrdx0 ▸ hs_eq]
        congr 1
        rcases s₀.regs with ⟨⟩
        simp [hs_nil]⟩
    · simpa only [hd_nil, hs_nil] using hmem
  · have hv_pos : 1 ≤ g.srcBytes.length := Nat.pos_of_ne_zero hv0
    have hbound : g.srcBytes.length ≤ 2 ^ 64 := Nat.le_of_lt (hrdx ▸ s.regs.rdx.toBitVec.isLt)
    have hdb : (g.dstBytes.take 1).length = 1 := List.length_take_of_le (by omega)
    have hsb : (g.srcBytes.take 1).length = 1 := List.length_take_of_le (by omega)
    obtain ⟨hsrc_mem, hdst_mem⟩ := split_loop_mem hv_pos hbound hdl hmem
    rw [← hrsi] at hsrc_mem
    rw [← hrdi] at hdst_mem
    sym => kstep; tactic =>
    rename_i w af
    have hcond : (w == BitVec.zero 64) = false := by
      simp only [w, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne]
      grind
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    sym =>
    kstep
    case h_mem => tactic => dsimp +zetaDelta only; exact hsrc_mem
    case h_len => exact hsb
    kstep
    case h_mem => tactic => dsimp +zetaDelta only; exact hdst_mem
    case h_len => exact hdb
    kstep 4
    tactic =>
    refine .done _ (.inr
      ⟨⟨g.dst + 1, g.src + 1, g.dstBytes.drop 1, g.srcBytes.drop 1,
        Eq ((g.srcBytes.take 1).At g.dst.toBitVec) ⋆
          (Eq ((g.srcBytes.take 1).At g.src.toBitVec) ⋆ g.frame)⟩,
      ⟨rfl, by simp [hdl], ?_, ?_, ?_⟩, by simp only [InvImage, List.length_drop]; omega,
      fun _ => donePost_of_take_drop _ s₀ hv_pos hbound⟩)
    · dsimp +zetaDelta only
      grind
    · dsimp +zetaDelta only
      simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact ⟨{ toBitVec := rcx.toBitVec.replaceLow
                 (BitVec.ofInt 8 (Int.ofBytes (g.srcBytes.take 1))) }, _, by
        rw [hs_eq]
        congr 1⟩
    · dsimp +zetaDelta only
      have hlow :
          BitVec.setWidth 8
            (s.regs.rcx.toBitVec.replaceLow (BitVec.ofInt 8 (Int.ofBytes (g.srcBytes.take 1)))) =
            BitVec.ofInt 8 (Int.ofBytes (g.srcBytes.take 1)) := by
        dsimp only [BitVec.replaceLow]
        bv_decide
      simp only [BitVec.setWidth_eq, hlow]
      have hst := Mem.storeInt_sep s.regs.rdi.toBitVec 1 (g.dstBytes.take 1) _ s.dmem
        ⟨hdst_mem, hdb⟩ (BitVec.ofInt 8 (Int.ofBytes (g.srcBytes.take 1))).toInt
      have hsb_eq : Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes (g.srcBytes.take 1))).toInt =
          g.srcBytes.take 1 :=
        (UInt8.toBytes_ofBytes _ (by omega)).trans (List.take_of_length_le (by omega))
      rw [hrdi, hsb_eq, sep_comm_l] at hst
      simpa only [hrdi, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, sep_assoc] using hst

private theorem memcpy_qword_loop {l : Layout} [l.WellFormed memcpy] (s₀ : MachineData)
    (g₀ : LoopGhost) (st₀ : MachineState)
    (h₀ : LoopInv ((l.apply memcpy).addrOf 2) s₀ g₀ st₀) :
    Eventually (step1 (l.apply memcpy))
      (DonePost ((l.apply memcpy).addrOf 20) s₀ g₀) st₀ := by
  refine tailrec_loop
    (InvImage.wf (r := (· < ·)) (fun g : LoopGhost => g.srcBytes.length) Nat.lt_wfRel.wf)
    (fun g ⟨s, pc⟩ hinv => ?_) g₀ h₀
  obtain ⟨rfl, hdl, hrdx, ⟨rcx, status, hs_eq⟩, hmem⟩ := hinv
  dsimp only at hdl hrdx hs_eq hmem
  have hrsi : s.regs.rsi = g.src := by rw [congrArg MachineData.regs hs_eq]
  have hrdi : s.regs.rdi = g.dst := by rw [congrArg MachineData.regs hs_eq]
  by_cases hv8 : g.srcBytes.length < 8
  · sym => kstep; tactic =>
    rename_i w status₁
    have hjb : (w.unsigned != s.regs.rdx.toBitVec.unsigned - (8#64).unsigned) = true := by
      simp only [w, Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, cf_sub_eq]
      simpa [hrdx] using hv8
    simp only [hjb, ↓reduceIte]
    sym => kstep 0; tactic =>
    refine eventually_weaken _ _ _ _ (fun _ => Or.inl)
      (memcpy_byte_loop s₀ g _ ⟨rfl, hdl, hrdx, ?_, hmem⟩)
    refine ⟨rcx, status₁, ?_⟩
    rw [hs_eq]
  · have hge8 : 8 ≤ g.srcBytes.length := Nat.le_of_not_lt hv8
    have hbound : g.srcBytes.length ≤ 2 ^ 64 := Nat.le_of_lt (hrdx ▸ s.regs.rdx.toBitVec.isLt)
    have hd8 : (g.dstBytes.take 8).length = 8 := List.length_take_of_le (by omega)
    have hs8 : (g.srcBytes.take 8).length = 8 := List.length_take_of_le (by omega)
    obtain ⟨hsrc_mem, hdst_mem⟩ := split_loop_mem hge8 hbound hdl hmem
    rw [← hrsi] at hsrc_mem
    rw [← hrdi] at hdst_mem
    sym => kstep; tactic =>
    rename_i w status₁
    have hjb : (w.unsigned != s.regs.rdx.toBitVec.unsigned - (8#64).unsigned) = false := by
      simp only [w, Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, cf_sub_eq]
      simpa [hrdx] using hge8
    simp only [hjb, Bool.false_eq_true, ↓reduceIte]
    sym =>
    kstep
    case h_mem => tactic => dsimp +zetaDelta only; exact hsrc_mem
    case h_len => exact hs8
    kstep
    case h_mem => tactic => dsimp +zetaDelta only; exact hdst_mem
    case h_len => exact hd8
    kstep 4
    tactic =>
    refine .done _ (.inr
      ⟨⟨g.dst + 8, g.src + 8, g.dstBytes.drop 8, g.srcBytes.drop 8,
        Eq ((g.srcBytes.take 8).At g.dst.toBitVec) ⋆
          (Eq ((g.srcBytes.take 8).At g.src.toBitVec) ⋆ g.frame)⟩,
      ⟨rfl, by simp [hdl], ?_, ?_, ?_⟩, by simp only [InvImage, List.length_drop]; omega,
      fun _ => donePost_of_take_drop _ s₀ hge8 hbound⟩)
    · dsimp +zetaDelta only
      grind
    · dsimp +zetaDelta only
      simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact ⟨{ toBitVec := BitVec.ofInt 64 (Int.ofBytes (g.srcBytes.take 8)) }, _, by
        rw [hs_eq]
        congr 1
        rcases s₀.regs with ⟨⟩
        dsimp only
        congr 1
        · exact UInt64.add_comm 8 g.src
        · exact UInt64.add_comm 8 g.dst⟩
    · dsimp +zetaDelta only
      simp only [BitVec.setWidth_eq]
      have hst := Mem.storeInt_sep s.regs.rdi.toBitVec 8 (g.dstBytes.take 8) _ s.dmem
        ⟨hdst_mem, hd8⟩ (BitVec.ofInt 64 (Int.ofBytes (g.srcBytes.take 8))).toInt
      have hs8_eq : Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes (g.srcBytes.take 8))).toInt =
          g.srcBytes.take 8 :=
        (UInt64.toBytes_ofBytes _ (by omega)).trans (List.take_of_length_le (by omega))
      rw [hrdi, hs8_eq, sep_comm_l] at hst
      simpa only [hrdi, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, sep_assoc] using hst

theorem memcpy_spec {l : Layout} {prog : Program} [l.WellFormed prog] (hp : memcpy <:+: prog)
    (dstBytes srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "memcpy" (MemcpyPre dstBytes srcBytes ra R) (MemcpyPost srcBytes ra R) := by
  obtain ⟨p₁, p₂, hprog⟩ := hp
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have hra_len : raBytes.length = 8 := Int.toBytes_length 8 _
  refine ⟨_, label?_infix p₁ memcpy p₂ hprog (k := 0) rfl, fun s ⟨hdl, hsl, hmem⟩ => ?_⟩
  refine lift_infix p₁ memcpy p₂ hprog fun [_] => ?_
  dsimp only [Reg64s.get64] at hmem
  have hmem' : s.dmem =⋆ Eq (dstBytes.At s.regs.rdi.toBitVec) ⋆
      (Eq (srcBytes.At s.regs.rsi.toBitVec) ⋆ (Eq (raBytes.At s.regs.rsp.toBitVec) ⋆ R)) := by
    simp only [sep_assoc] at hmem
    rwa [sep_comm_l (Eq (raBytes.At _)),
      sep_comm_l (Eq (raBytes.At _)) (Eq (srcBytes.At _))] at hmem
  refine eventually_trans _
    (LoopInv (((l.drop p₁).apply memcpy).addrOf 2) s
      ⟨s.regs.rdi, s.regs.rsi, dstBytes, srcBytes, Eq (raBytes.At s.regs.rsp.toBitVec) ⋆ R⟩)
    _ _ ?_ ?_
  · sym => kstep 1; tactic =>
    refine .done _ ⟨rfl, hdl.trans hsl.symm, hsl.symm, ⟨s.regs.rcx, s.status, ?_⟩, hmem'⟩
    rcases s with ⟨⟨⟩, _, _, _, _⟩
    rfl
  · intro st₁ hinv₁
    refine eventually_trans _ _ _ _ (memcpy_qword_loop s _ st₁ hinv₁) ?_
    rintro ⟨t, pc⟩ ⟨rfl, ⟨rcx, st, ht_eq⟩, ht_mem⟩
    dsimp only at ht_eq ht_mem
    have ht_rsp : t.regs.rsp = s.regs.rsp := by rw [congrArg MachineData.regs ht_eq]
    have ht_ra : t.dmem =⋆ Eq (raBytes.At t.regs.rsp.toBitVec) ⋆
        (Eq (srcBytes.At s.regs.rdi.toBitVec) ⋆ Eq (srcBytes.At s.regs.rsi.toBitVec) ⋆ R) := by
      rw [ht_rsp]
      dsimp +zetaDelta only at ht_mem ⊢
      ecancel
    sym => kstep; tactic =>
    refine .done _ ⟨?_, ⟨rcx, st, ?_⟩, ?_⟩
    · dsimp only
      rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    · dsimp +zetaDelta only [Reg64s.get64, Reg64s.set64]
      have hrdx_len : UInt64.ofNat srcBytes.length = s.regs.rdx := by
        rw [hsl]
        exact UInt64.ofNat_toNat
      rw [hrdx_len] at ht_eq
      rw [ht_eq]
      rcases s with ⟨⟨⟩, _, _, _, _⟩
      rfl
    · dsimp only [Reg64s.get64]
      rw [ht_rsp] at ht_ra
      simpa only [sep_assoc] using ht_ra

def copyCaller : Program := ⸨prog|
copy_caller:
  call memcpy
  ret
⸩

def CopyCallerPre (dstBytes srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop)
    (s : MachineData) : Prop :=
  ∃ slot : List UInt8, slot.length = 8 ∧
    dstBytes.length = s.regs.rdx.toNat ∧
    srcBytes.length = s.regs.rdx.toNat ∧
    (s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆
      Eq (slot.At (s.regs.get64 .rsp - 8#64)) ⋆
      Eq (dstBytes.At (s.regs.get64 .rdi)) ⋆
      Eq (srcBytes.At (s.regs.get64 .rsi)) ⋆ R)

def CopyCallerPost (srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop)
    (s : MachineData) (u : MachineState) : Prop :=
  u.pc = ra ∧
    (∃ rcx status, u.data = { s with
      regs := { s.regs with
        rax := s.regs.rdi
        rcx := rcx
        rdx := 0
        rsi := s.regs.rsi + s.regs.rdx
        rdi := s.regs.rdi + s.regs.rdx
        rsp := s.regs.rsp + 8 }
      status
      dmem := u.data.dmem }) ∧
    ∃ slot : List UInt8, slot.length = 8 ∧
      (u.data.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (s.regs.get64 .rsp)) ⋆
        Eq (slot.At (s.regs.get64 .rsp - 8#64)) ⋆
        Eq (srcBytes.At (s.regs.get64 .rdi)) ⋆
        Eq (srcBytes.At (s.regs.get64 .rsi)) ⋆ R)

theorem copyCaller_spec {l : Layout} {prog : Program} [l.WellFormed prog]
    (hp : copyCaller <:+: prog)
    (hmemcpy : ∀ dstBytes srcBytes ra R,
      Spec l prog "memcpy" (MemcpyPre dstBytes srcBytes ra R) (MemcpyPost srcBytes ra R))
    (dstBytes srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop) :
    Spec l prog "copy_caller" (CopyCallerPre dstBytes srcBytes ra R)
      (CopyCallerPost srcBytes ra R) := by
  obtain ⟨p₁, p₂, hprog⟩ := hp
  let ef := (l.drop p₁).apply copyCaller
  let raBytes := Int.toBytes 8 ra.toBitVec.toInt
  have hra_len : raBytes.length = 8 := Int.toBytes_length 8 _
  have haddr0 : ef.addrOf 0 = ef.addrOf 1 :=
    ((ef.addrOf_succ (n := 0) rfl).trans (Int64.add_zero _)).symm
  refine ⟨_, label?_infix p₁ copyCaller p₂ hprog (k := 0) rfl,
    fun s ⟨slot, hslot, hdl, hsl, hmem⟩ => ?_⟩
  rw [haddr0]
  have hmem_slot : s.dmem =⋆ Eq (slot.At (s.regs.get64 .rsp - 8#64)) ⋆
      (Eq (dstBytes.At (s.regs.get64 .rdi)) ⋆ Eq (srcBytes.At (s.regs.get64 .rsi)) ⋆
        (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R)) := by
    dsimp +zetaDelta only at hmem ⊢
    ecancel
  obtain ⟨entry, hlbl, hrun⟩ := hmemcpy dstBytes srcBytes (ef.addrOf 2)
    (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R)
  have hv := Mem.loadInt_sep slot _ 8 _ _ hmem_slot hslot (by decide)
  apply step_at_infix p₁ copyCaller p₂ hprog (k := 1) rfl
  letI := Executable.labels (l.apply prog)
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Effects.All_resolve_label, hlbl,
    Effects.All_require_write_access, Width.bytes, Width.bytesv, Width.bits, hv, Effects.All,
    Int64.add_sub_cancel_left, Int64.ofBitVec_toBitVec]
  have hcall_mem :
      Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (ef.addrOf 2).toBitVec.toInt =⋆
        Eq ((Int.toBytes 8 (ef.addrOf 2).toBitVec.toInt).At (s.regs.get64 .rsp - 8#64)) ⋆
          (Eq (dstBytes.At (s.regs.get64 .rdi)) ⋆ Eq (srcBytes.At (s.regs.get64 .rsi)) ⋆
            (Eq (raBytes.At (s.regs.get64 .rsp)) ⋆ R)) :=
    Mem.storeInt_sep _ 8 slot _ s.dmem ⟨hmem_slot, hslot⟩ _
  refine eventually_trans _ _ _ _ (hrun _ ⟨by simpa only [Reg64s.set64] using hdl,
    by simpa only [Reg64s.set64] using hsl, by
      simpa only [MemcpyPre, Reg64s.get64, Reg64s.set64, sep_assoc] using hcall_mem⟩) ?_
  rintro ⟨t, pc⟩ ⟨rfl, ⟨rcx, st, ht⟩, ht_mem⟩
  dsimp only [Reg64s.get64, Reg64s.set64] at ht ht_mem
  have hrsp_sub : ({ toBitVec := s.regs.rsp.toBitVec - 8#64 } : UInt64) + 8 = s.regs.rsp :=
    UInt64.sub_add_cancel s.regs.rsp 8
  rw [hrsp_sub] at ht
  have ht_rsp : t.regs.rsp = s.regs.rsp := by rw [congrArg MachineData.regs ht]
  let slot' := Int.toBytes 8 (ef.addrOf 2).toBitVec.toInt
  have hslot' : slot'.length = 8 := Int.toBytes_length 8 _
  have ht_ra :
      t.dmem =⋆
        Eq (raBytes.At t.regs.rsp.toBitVec) ⋆
          (Eq (slot'.At (s.regs.rsp.toBitVec - 8#64)) ⋆
            Eq (srcBytes.At s.regs.rdi.toBitVec) ⋆ Eq (srcBytes.At s.regs.rsi.toBitVec) ⋆ R) := by
    rw [ht_rsp]
    simp only [sep_assoc] at ht_mem
    rw [sep_comm_l (Eq (srcBytes.At s.regs.rsi.toBitVec)),
      sep_comm_l (Eq (srcBytes.At s.regs.rdi.toBitVec)),
      sep_comm_l (Eq (slot'.At _))] at ht_mem
    simpa only [sep_assoc] using ht_mem
  apply lift_infix p₁ copyCaller p₂ hprog
  sym => kstep; tactic =>
  refine .done _ ⟨?_, ⟨rcx, st, ?_⟩, slot', hslot', ?_⟩
  · dsimp only
    rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
  · dsimp +zetaDelta only [Reg64s.get64, Reg64s.set64]
    rw [ht]
    rcases s with ⟨⟨⟩, _, _, _, _⟩
    rfl
  · dsimp only [Reg64s.get64] at ht_ra ⊢
    rw [ht_rsp] at ht_ra
    simpa only [sep_assoc] using ht_ra

def concreteLayout : Layout :=
  { start := 0x1000, instrSize := fun _ => 5, instrSize_pos := fun _ => by decide }

example (dstBytes srcBytes : List UInt8) (ra : Int64) (R : DataMem → Prop) :
    let prog := memcpy ++ copyCaller
    Spec concreteLayout prog "memcpy" (MemcpyPre dstBytes srcBytes ra R)
        (MemcpyPost srcBytes ra R) ∧
      Spec concreteLayout prog "copy_caller" (CopyCallerPre dstBytes srcBytes ra R)
          (CopyCallerPost srcBytes ra R) :=
  let prog := memcpy ++ copyCaller
  haveI : concreteLayout.WellFormed prog := by decide
  have hmc := fun d s ra' R' =>
    memcpy_spec (l := concreteLayout) (prog := prog) (by decide) d s ra' R'
  ⟨hmc dstBytes srcBytes ra R,
   copyCaller_spec (l := concreteLayout) (prog := prog) (by decide) hmc dstBytes srcBytes ra R⟩

end Spec.Examples.Memcpy
