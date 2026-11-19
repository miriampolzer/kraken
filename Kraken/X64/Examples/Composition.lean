module

public import Lean
import Kraken.X64.Parser
import Kraken.X64.OmniSemantics
import Kraken

open Kraken (Layout)

/-- Swaps `rax` and `rbx`-/
def swap := ⸨prog|
swap: xor %rax, %rbx
      xor %rbx, %rax
      xor %rax, %rbx
      jmp %rcx
⸩

theorem swap.sem (l : Layout) [l.WellFormed swap]
  (st : MachineData) :
    let e : Executable := l.apply swap
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        ∃ status,
        st' = {st with
          regs := {st.regs with
            rax := st.regs.rbx
            rbx := st.regs.rax
          }
          status
        } ∧
        pc.toUInt64 = st.regs.rcx
      )
      ⟨st, l.start⟩ := by
  kprologue swap with st
  dsimp only
  sym => kstep; tactic =>
  apply Eventually.done
  rename_i a _ b _ c _
  simp [a, b, c]
  bv_decide


def client := ⸨prog|
  La: mov $41, %rax
      mov $42, %rbx
      mov $Lb,  %rcx

      jmp swap

  Lb: test %rax, %rbx
⸩

def final := client ++ swap

theorem final.sem (l : Layout) [hwf : l.WellFormed final]
  (st : MachineData) :
    let e : Executable := l.apply final
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        pc = e.addrOf (client.length) ∧
        st'.regs.rax = 42 ∧
        st'.regs.rbx = 41)
      ⟨st, l.start⟩ := by
  haveI : l.WellFormed (client ++ swap) := hwf
  kprologue final with st
  sym => kstep 4; tactic =>
  have addrOf_7 : (l.drop client).start = (l.apply final).addrOf 7 := rfl
  refine eventually_trans _ _ _ _
    (Eventually.prepend client swap _ _ (addrOf_7 ▸ swap.sem (l.drop client) _)) ?_
  rintro ⟨st2, pc⟩ ⟨_, rfl, pc_toUInt64⟩
  dsimp at *
  have addrOf_5 : pc = (l.apply final).addrOf 5 := by bv_decide
  rw [addrOf_5]
  sym => kstep 1; tactic =>
  apply Eventually.done
  simp [client]
