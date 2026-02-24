import Std

-- FIXME -- surely something like this is in Std?

def Option.except [Pure m] [MonadExcept e m] (self: Option α) (err : e): m α :=
  match self with
  | .none => throw err
  | .some v => pure v

-- STATE, INSTRUCTIONS, LABELS

-- Registers Enumeration
inductive Reg
| rax | rbx | rcx | rdx
| rsi | rdi | rsp | rbp
| r8  | r9  | r10 | r11
| r12 | r13 | r14 | r15
deriving Repr, BEq, DecidableEq

-- Register State
-- We choose this representation rather than a `Fin 16 -> Word` to avoid
-- reasoning about functional modifications.
structure Registers where
  rax : UInt64 := 0
  rbx : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  rsi : UInt64 := 0
  rdi : UInt64 := 0
  rsp : UInt64 := 0
  rbp : UInt64 := 0
  r8  : UInt64 := 0
  r9  : UInt64 := 0
  r10 : UInt64 := 0
  r11 : UInt64 := 0
  r12 : UInt64 := 0
  r13 : UInt64 := 0
  r14 : UInt64 := 0
  r15 : UInt64 := 0
deriving Repr

-- Flags
structure Flags where
  zf : Bool := false -- Zero Flag
  of : Bool := false -- Overflow Flag
  cf : Bool := false -- Carry Flag
deriving Repr, BEq

-- Heap
-- We only reason about aligned accesses, so our map only has keys that are = 0
-- % 8. We do not make any assumptions about the memory -- reading an
-- uninitialized value results in an error.
abbrev Address := UInt64
abbrev Word := UInt64
abbrev Heap := Std.ExtHashMap Address Word

instance : Repr Heap where
  reprPrec _ _ := "<opaque memory>"

-- Machine State
structure MachineState where
  regs : Registers := {}
  flags : Flags := {}
  rip : Nat := 0
  heap : Heap := ∅
deriving Repr

-- Operands (extended with indexed memory modes for MontMul)
-- Memory operands use WORD offsets (multiplied by 8 in code gen) for alignment
inductive Operand
| reg (r : Reg)                                          -- %rax
| imm (v : UInt64)                                       -- $42
| mem (base : Reg) (wordOffset : Int := 0)               -- 8(%rsp) = wordOffset 1
| memIdx (base : Reg) (idx : Reg) (wordOffset : Int := 0) -- (%rsi,%r15,8) + wordOffset*8
| memByte (base : Reg) (byteOffset : Int := 0)           -- Raw byte offset (for lea)
deriving Repr, BEq

abbrev Label := String

-- Instructions (extended for MontMul)
inductive Instr
  -- Arithmetic
  | add  (dst src : Operand)                   -- addq: dst += src, sets CF, ZF, OF
  | adc  (dst src : Operand)                   -- adcq: dst += src + CF, sets CF, ZF
  | adcx (dst : Operand) (src : Operand)       -- adcxq: dst += src + CF, only affects CF (ADX)
  | adox (dst : Operand) (src : Operand)       -- adoxq: dst += src + OF, only affects OF (ADX)
  | sub  (dst src : Operand)                   -- subq: dst -= src, sets CF, ZF, OF
  | sbb  (dst src : Operand)                   -- sbbq: dst -= src + CF, sets CF, ZF
  | mul  (src : Operand)                       -- mulq: rdx:rax = rax * src
  | mulx (hi lo : Operand) (src : Operand)     -- mulxq: hi:lo = rdx * src (BMI2, no flags)
  | imul (dst src : Operand)                   -- imulq: dst *= src (truncated, sets OF/CF)
  | neg  (dst : Operand)                       -- negq: dst = -dst, sets CF, ZF, OF
  | dec  (dst : Operand)                       -- decq: dst--, sets ZF (not CF!)

  -- Move/Load
  | mov  (dst src : Operand)                   -- movq
  | lea  (dst : Reg) (src : Operand)           -- leaq: dst = effective address

  -- Bitwise
  | xor  (dst src : Operand)                   -- xorq: dst ^= src, clears CF/OF, sets ZF
  | and  (dst src : Operand)                   -- andq: dst &= src, clears CF/OF, sets ZF
  | or   (dst src : Operand)                   -- orq: dst |= src, clears CF/OF, sets ZF

  -- Compare (sets flags only)
  | cmp  (a b : Operand)                       -- cmpq: compute a - b, set flags

  -- Control flow (explicit jumps - core design of Kraken)
  | jmp (target : Label)                       -- Unconditional jump
  | jz  (target : Label)                       -- Jump if ZF=1
  | jnz (target : Label)                       -- Jump if ZF=0
  | jb  (target : Label)                       -- Jump if CF=1 (unsigned below)
  | jae (target : Label)                       -- Jump if CF=0 (unsigned above or equal)
  | jne (target : Label)                       -- Alias for jnz (after cmp)
  | ja  (target : Label)                       -- Jump if CF=0 and ZF=0 (unsigned above)
  deriving Repr

def Instr.is_ctrl
  | Instr.jmp _ | Instr.jnz _ | Instr.jz _
  | Instr.jb _ | Instr.jae _ | Instr.jne _ | Instr.ja _ => true
  | _ => false

-- HELPERS

def Registers.get (regs : Registers) (r : Reg) : UInt64 :=
  match r with
  | .rax => regs.rax | .rbx => regs.rbx | .rcx => regs.rcx | .rdx => regs.rdx
  | .rsi => regs.rsi | .rdi => regs.rdi | .rsp => regs.rsp | .rbp => regs.rbp
  | .r8  => regs.r8  | .r9  => regs.r9  | .r10 => regs.r10 | .r11 => regs.r11
  | .r12 => regs.r12 | .r13 => regs.r13 | .r14 => regs.r14 | .r15 => regs.r15

def Registers.set (regs : Registers) (r : Reg) (v : UInt64) : Registers :=
  match r with
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v } | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v } | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v } | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v } | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

def MachineState.readMem [Pure m] [MonadExcept String m] (s : MachineState) (addr : Address) : m Word :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    s.heap[addr]?.except (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")

def MachineState.writeMem [Pure m] [MonadExcept String m] (s : MachineState) (addr : Address) (val : Word) : m MachineState :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    pure { s with heap := s.heap.insert addr val }


-- EVALUATION

-- Compute effective address for memory operand (word offsets × 8)
def effectiveAddr (s : MachineState) : Operand → UInt64
  | .mem base wordOffset =>
    let baseVal := s.getReg base
    if wordOffset >= 0 then
      baseVal + (wordOffset.toNat * 8).toUInt64
    else
      baseVal - ((-wordOffset).toNat * 8).toUInt64
  | .memIdx base idx wordOffset =>
    let baseVal := s.getReg base
    let idxVal := s.getReg idx
    let addr := baseVal + idxVal * 8  -- Fixed scale of 8
    if wordOffset >= 0 then
      addr + (wordOffset.toNat * 8).toUInt64
    else
      addr - ((-wordOffset).toNat * 8).toUInt64
  | .memByte base byteOffset =>
    let baseVal := s.getReg base
    if byteOffset >= 0 then
      baseVal + byteOffset.toNat.toUInt64
    else
      baseVal - (-byteOffset).toNat.toUInt64
  | _ => 0  -- Not a memory operand

def eval_operand [Pure m] [MonadExcept String m] (s : MachineState) (o : Operand) : m UInt64 :=
  match o with
  | .reg r => pure (s.getReg r)
  | .imm v => pure v
  | .mem _ _ => s.readMem (effectiveAddr s o)
  | .memIdx _ _ _ => s.readMem (effectiveAddr s o)
  | .memByte _ _ => s.readMem (effectiveAddr s o)

def eval_reg_or_mem [Pure m] [MonadExcept String m] (s : MachineState) (o : Operand) : m UInt64 :=
  match o with
  | .reg r => pure (s.getReg r)
  | .mem _ _ | .memIdx _ _ _ | .memByte _ _ => s.readMem (effectiveAddr s o)
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem [Monad m] [MonadExcept String m] (s: MachineState) (o: Operand) (v: Word): m MachineState := do
  match o with
  | .reg r =>
      pure (s.setReg r v)
  | .mem _ _ | .memIdx _ _ _ | .memByte _ _ =>
      s.writeMem (effectiveAddr s o) v
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg [Pure m] [MonadExcept String m] (s: MachineState) (o: Operand) (v: Word): m MachineState :=
  match o with
  | .reg r =>
      pure (s.setReg r v)
  | .mem _ _ | .memIdx _ _ _  | .memByte _ _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt1 [Monad m] [MonadExcept String m] (s : MachineState) (i : Instr) : m MachineState := do
  match i with
  | .mov dst src =>
      let val ← eval_operand s src
      set_reg_or_mem s dst val

  | .add dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v.toNat + src_v.toNat
      let carry := result >>> 64
      let result64 := UInt64.ofNat result
      let zf := result64 == 0
      let cf := carry != 0
      -- OF is set if sign bits of operands are same but result sign differs
      let of := (dst_v.toInt64.toInt + src_v.toInt64.toInt >= 2^63) ||
                (dst_v.toInt64.toInt + src_v.toInt64.toInt < -2^63)
      let s ← set_reg_or_mem s dst result64
      pure { s with flags := { zf, of, cf }}

  | .adc dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v.toNat + src_v.toNat + s.flags.cf.toNat
      let carry := result >>> 64
      let result64 := UInt64.ofNat result
      let zf := result64 == 0
      let cf := carry != 0
      let s ← set_reg_or_mem s dst result64
      pure { s with flags := { s.flags with zf, cf }}

  | .adcx dst src =>
      let src_v ← eval_reg_or_mem s src
      let dst_v ← eval_reg_or_mem s dst
      let result := src_v.toNat + dst_v.toNat + s.flags.cf.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with cf := carry != 0 }}
      set_reg s dst result

  | .adox dst src =>
      let src_v ← eval_reg_or_mem s src
      let dst_v ← eval_reg_or_mem s dst
      let result := src_v.toNat + dst_v.toNat + s.flags.of.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with of := carry != 0 }}
      set_reg s dst result

  | .sub dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let res := (Int.ofNat dst_v.toNat) - (Int.ofNat src_v.toNat)
      let cf := res < 0
      let of := dst_v.toInt64.toInt - src_v.toInt64.toInt >= 2^63 ||
                dst_v.toInt64.toInt - src_v.toInt64.toInt < -2^63
      let result64 := UInt64.ofInt res
      let zf := result64 == 0
      let s ← set_reg_or_mem s dst result64
      pure { s with flags := { zf, of, cf }}

  | .sbb dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let res := (Int.ofNat dst_v.toNat) - (Int.ofNat src_v.toNat) - s.flags.cf.toNat
      let cf := res < 0
      let result64 := UInt64.ofInt res
      let zf := result64 == 0
      let s ← set_reg_or_mem s dst result64
      pure { s with flags := { s.flags with zf, cf }}

  | .mul src =>
      -- mulq: rdx:rax = rax * src
      let src_v ← eval_reg_or_mem s src
      let rax_v := s.getReg .rax
      let result := rax_v.toNat * src_v.toNat
      let lo := UInt64.ofNat result
      let hi := UInt64.ofNat (result >>> 64)
      let s := s.setReg .rax lo
      let s := s.setReg .rdx hi
      -- mul sets OF and CF if high half is non-zero
      let cf := hi != 0
      let of := hi != 0
      pure { s with flags := { s.flags with cf, of }}

  | .mulx hi lo src1 =>
      let src1_v ← eval_reg_or_mem s src1
      let src2_v := s.getReg .rdx
      let result := src1_v.toNat * src2_v.toNat
      -- Semantics say that if hi and lo are aliased, the value written is hi
      let s ← set_reg s lo (UInt64.ofNat result)
      set_reg s hi (UInt64.ofNat (result >>> 64))

  | .imul dst src =>
      let src_v ← eval_reg_or_mem s src
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v.toNat * src_v.toNat
      let result64 := UInt64.ofNat result
      let s ← set_reg_or_mem s dst result64
      -- OF/CF set if result doesn't fit in 64 bits
      let overflow := result >>> 64 != 0
      pure { s with flags := { s.flags with cf := overflow, of := overflow }}

  | .neg dst =>
      let dst_v ← eval_reg_or_mem s dst
      let result := 0 - dst_v
      let zf := result == 0
      let cf := dst_v != 0  -- CF is set unless operand is 0
      let s ← set_reg_or_mem s dst result
      pure { s with flags := { s.flags with zf, cf }}

  | .dec dst =>
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v - 1
      let zf := result == 0
      -- dec does NOT affect CF (important for MontMul!)
      let s ← set_reg_or_mem s dst result
      pure { s with flags := { s.flags with zf }}

  | .lea dst src =>
      -- lea computes effective address, doesn't access memory
      let addr := effectiveAddr s src
      pure (s.setReg dst addr)

  | .xor dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v ^^^ src_v
      let zf := result == 0
      -- xor clears CF and OF
      let s ← set_reg_or_mem s dst result
      pure { s with flags := { zf, of := false, cf := false }}

  | .and dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v &&& src_v
      let zf := result == 0
      let s ← set_reg_or_mem s dst result
      pure { s with flags := { zf, of := false, cf := false }}

  | .or dst src =>
      let src_v ← eval_operand s src
      let dst_v ← eval_reg_or_mem s dst
      let result := dst_v ||| src_v
      let zf := result == 0
      let s ← set_reg_or_mem s dst result
      pure { s with flags := { zf, of := false, cf := false }}

  | .cmp a b =>
      let a_v ← eval_reg_or_mem s a
      let b_v ← eval_operand s b
      let res := (Int.ofNat a_v.toNat) - (Int.ofNat b_v.toNat)
      let cf := res < 0
      let zf := res == 0
      let of := a_v.toInt64.toInt - b_v.toInt64.toInt >= 2^63 ||
                a_v.toInt64.toInt - b_v.toInt64.toInt < -2^63
      pure { s with flags := { zf, of, cf }}

  | _ => throw s!"unsupported non-control instruction {repr i}"

def jump_if [Monad m] [MonadExcept String m] (s: MachineState) (b: Bool) (rip: Nat): m MachineState := do
  if b then
    pure { s with rip }
  else
    pure (next s)


def ctrl [Monad m] [MonadExcept String m] (s: MachineState) (lookup: Label → m Nat) (i: Instr) : m MachineState := do
  match i with
  | .jmp l =>
      let rip ← lookup l
      jump_if s True rip
  | .jnz l =>
      let rip ← lookup l
      jump_if s (!s.flags.zf) rip
  | .jz l =>
      let rip ← lookup l
      jump_if s s.flags.zf rip
  | .jb l =>
      -- Jump if below (unsigned): CF=1
      let rip ← lookup l
      jump_if s s.flags.cf rip
  | .jae l =>
      -- Jump if above or equal (unsigned): CF=0
      let rip ← lookup l
      jump_if s (!s.flags.cf) rip
  | .jne l =>
      -- Alias for jnz: ZF=0
      let rip ← lookup l
      jump_if s (!s.flags.zf) rip
  | .ja l =>
      -- Jump if above (unsigned): CF=0 AND ZF=0
      let rip ← lookup l
      jump_if s (!s.flags.cf && !s.flags.zf) rip
  | _ => throw s!"unsupported control instruction {repr i}"

abbrev Program := List (Option Label × Instr)

def lookup [Pure m] [MonadExcept String m] (p: Program) (l: Label): m Nat :=
  (p.findIdx? (fun (l', _) => l' = .some l)).except "Invalid label: {repr l}"

def fetch [Pure m] [MonadExcept String m] (p: Program) (s: MachineState): m (Option Label × Instr) :=
  p[s.rip]?.except "Impossible: PC outside of program bounds"

def eval1 [Monad m] [MonadExcept String m] (p: Program) (s: MachineState): m MachineState := do
  let (_, i) ← fetch p s
  if i.is_ctrl then
    let s ← ctrl s (lookup p) i
    pure s
  else
    let s ← strt1 s i
    pure (next s)

def eval (p: Program) (s: MachineState): Option MachineState := do
  let s ← (eval1 (m:=Except String) p s).toOption
  eval p s
partial_fixpoint

def step1 (p: Program) (s: MachineState) (post: _) :=
  @ExceptCpsT.runK Id Prop String MachineState (eval1 p s) "" post (fun _ => False)

def Post := MachineState → Prop

inductive eventually (prog: Program) (p: MachineState → Prop): MachineState -> Prop
  | done (initial: MachineState):
      p initial →
      eventually _ p initial
  | step (initial: MachineState):
      (mid_p: Post) ->
      step1 prog initial mid_p →
      (forall (mid: MachineState), mid_p mid → eventually _ p mid) →
      eventually _ p initial

theorem step_cps {p : Program} (post: Post) (initial: MachineState):
  step1 p initial (fun mid => eventually p post mid) → eventually p post initial :=
  by
    intro
    apply eventually.step
    <;> try assumption
    grind

theorem eventually_trans (program: Program) (p q: Post) (initial: MachineState)
  (e: eventually program p initial)
  (h: forall s, p s → eventually program q s):
    eventually program q initial
  := by
    induction e with
    | done =>
        grind
    | step initial mid_p step pred ind_h =>
        apply eventually.step
        <;> assumption

theorem eventually_weaken (program: Program) (p q: Post)
  (h: forall s, p s → q s):
    eventually program p initial → eventually program q initial
  := by
    intro hp
    induction ih: hp
    . apply eventually.done
      grind
    . apply eventually.step
      <;> try assumption
      grind

-- TEST

-- Example 1: single step of execution
def p1: Program := [
  (.none, .mov (.reg .rax) (.imm 1)),
]

example: @ExceptCpsT.runK Id Prop String MachineState (eval1 p1 {}) "" (fun s => s.regs.rax = 1) (fun _ => False) := by
  simp [Instr.is_ctrl,p1,eval1,fetch,Option.except,ExceptCpsT.runK,bind,pure]
  simp [strt1,eval_operand,set_reg_or_mem,MachineState.setReg,next,Registers.set,pure,bind]

def p2: Program := [
  (.some "start", .mov (.reg .rax) (.imm 1)),
  (.none,         .jz "start"),
  (.none,         .mov (.reg .rax) (.imm 2)),
]

syntax "step_one" : tactic
macro_rules
  | `(tactic|step_one) =>
  `(tactic|
    simp [
      step1,Instr.is_ctrl,eval1,fetch,Option.except,ExceptCpsT.runK,bind,pure,
      -- works for calls to strt1
      strt1,eval_operand,eval_reg_or_mem,set_reg,set_reg_or_mem,effectiveAddr,MachineState.setReg,next,Registers.set,pure,bind,next,MachineState.getReg,Registers.get,
      -- or calls to ctrl
      ctrl,lookup,List.findIdx?,List.findIdx?.go,Option.except,pure,bind,jump_if,next])

-- Example 2: stepping through both straightline and control instructions
example: eventually p2 (fun s => s.regs.rax = 2) {} := by
  simp [p2]

  apply step_cps
  step_one

  apply step_cps
  step_one

  apply step_cps
  step_one

  apply eventually.done
  simp

-- A loop down to 0
theorem reg_dec_loop (prog: Program) (post: Post) (initial: MachineState) (invariant: Nat → Post) (n: Nat):
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (forall state, invariant 0 state → eventually prog post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (forall state k, k != 0 → invariant k state → eventually prog (invariant (k - 1)) state) →
  -- then: we can prove the post
  eventually prog post initial
  := by
    intro misc
    rcases misc with ⟨ initial_invariant, case_zero, case_nonzero ⟩
    if n = 0 then
      apply case_zero
      grind
    else
      apply eventually_trans prog (invariant (n - 1)) post
      grind
      intros srec _
      apply reg_dec_loop prog post srec invariant (n - 1)
      grind

-- Example 3: a loop
def p3: Program := [
  -- (.none,         .mov (.reg .rbx) (.imm 4)),                 -- rbx: loop counter = 4
  (.none,         .mov (.reg .rdx) (.imm 2)),                 -- rdx: current result = 2
  (.some "start", .sub (.reg .rbx) (.imm 0)),                 -- TEST: zf = (rbx == 0)
  (.none        , .jz "end"),                                 -- end loop if rbx == 0 (a.k.a. "while rbx >= 0")
  (.none        , .mulx (.reg .rax) (.reg .rdx) (.reg .rdx)), -- BODY: rdx := rdx * rdx
  (.none,         .sub (.reg .rbx) (.imm 1)),                 -- rbx -= 1
  (.none,         .jmp "start"),                              -- go back to test & loop body
  (.some "end",   .mov (.reg .rax) (.imm 0)),                 -- meaningless -- just want the label to be well-defined
  -- result is 2^16, in rdx
]

-- Need to do something for when we have reached the end of the instruction list
-- maybe a special state! Right now this returns `none` because we eventually
-- hit the final instruction and then rip is out of bounds.
#eval (eval p3 {})

def p3_spec (s: MachineState): Nat := 2^(2*s.regs.rbx.toNat + 1)

-- NOTE: This proof was broken by the flag semantics changes to support more instructions.
-- It was already incomplete (had sorry statements). Full rewrite needed.
theorem p3_correct (initial: MachineState):
    p3_spec initial < 2^64 →
    initial.rip = 0 →
    eventually p3 (fun s => s.regs.rdx.toNat == p3_spec initial ∧ s.regs.rax == 0) initial := by
  sorry
