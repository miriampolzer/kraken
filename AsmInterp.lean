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

-- Instructions
inductive Operand
| reg (r : Reg)
| imm (v : UInt64)
| mem (addr : Address)
deriving Repr

abbrev Label := String

inductive Instr
| mov (dst : Operand) (src : Operand)
| mulx (hi : Operand) (lo : Operand) (src1: Operand)
| adcx (dst : Operand) (src : Operand)
| adox (dst : Operand) (src : Operand)
| sub (dst: Operand) (src: Operand)
| jnz (target : Label)
| jz (target : Label)
| jmp (target : Label)
deriving Repr

def Instr.is_ctrl
  | Instr.jmp _
  | Instr.jnz _
  | Instr.jz _ => true
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

class Throw α where
  throw: String → α

def throw [inst: Throw α] :=
  inst.throw

def MachineState.readMem [Throw α] (s : MachineState) (addr : Address) (ret: Word → α): α :=
  if addr % 8 != 0 then
    throw (s!"Out-of-bounds access (rip={repr s.rip})")
  else
    match s.heap[addr]? with
    | .some v => ret v
    | .none => throw (s!"Memory read but not written to (rip={repr s.rip}, addr={repr addr})")

def MachineState.writeMem [Throw α] (s : MachineState) (addr : Address) (val : Word) (ret: MachineState → α) : α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access (rip={repr s.rip})"
  else
    ret { s with heap := s.heap.insert addr val }

-- EVALUATION

def eval_operand [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .imm v => ret v
  | .mem a => s.readMem a ret

def eval_reg_or_mem [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .mem a => s.readMem a ret
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem a =>
      s.writeMem a v ret
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt1 [Throw α] (s : MachineState) (i : Instr) (ret: MachineState → α): α :=
  match i with
  | .mov dst src =>
      eval_operand s src (fun val =>
      set_reg_or_mem s dst val ret)

  | .adcx dst src =>
      -- Some thoughts: I basically try to assert the well-formedness of
      -- instructions (by asserting that e.g. immediate operands are not
      -- allowed, or that the x64 semantics demand that the destination of adcx
      -- be a general-purpose register... so that it at least simplifies the
      -- reasoning, but realistically, since we intend to consume source
      -- assembly (possibly with an actual frontend to parse .S syntax), the
      -- assembler will enforce eventually that no such nonsensical instructions
      -- exist. Is it worth the trouble?
      eval_reg_or_mem s src (fun src_v  =>
      eval_reg_or_mem s dst (fun dst_v  =>
      let result := src_v.toNat + dst_v.toNat + s.flags.cf.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with cf := carry != 0 }}
      set_reg s dst result ret))

  | .adox dst src =>
      eval_reg_or_mem s src (fun src_v  =>
      eval_reg_or_mem s dst (fun dst_v  =>
      -- TODO: figure out how to make sure that this let-binding does not get
      -- inlined, *unless* the right-hand side can be computed to a constant
      let result := src_v.toNat + dst_v.toNat + s.flags.of.toNat
      let carry := result >>> 64
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with of := carry != 0 }}
      set_reg s dst result ret))

  | .mulx hi lo src1 =>
      eval_reg_or_mem s src1 (fun src1  =>
      eval_reg_or_mem s (.reg .rdx) (fun src2  =>
      let result := src1.toNat * src2.toNat
      -- Semantics say that if hi and lo are aliased, the value written is hi
      set_reg s lo (UInt64.ofNat result) (fun s  =>
      set_reg s hi (UInt64.ofNat (result >>> 64)) ret)))

  | .sub dst src =>
      eval_operand s src (fun src1  =>
      if src matches .imm _ && src1.toNat >= 2^31 then
        throw "TODO: sign-extension" -- line "SUB r/m64, imm32" in the Intel spec
      else
        eval_reg_or_mem s dst (fun dst1  =>
        -- "The SUB instruction... sets the OF and CF flags to indicate an
        -- overflow in the signed or unsigned result, respectively. The SF flag
        -- indicates the sign of the signed result."
        --
        -- CF: interpret the operands as unsigned (toNat), then check for
        -- overflow (CF). Checking for overflow is done by converting to Int,
        -- since subtraction on Nats clamps to 0.
        let res := (Int.ofNat dst1.toNat) - (Int.ofNat src1.toNat)
        let cf := res < 0
        -- OF: interpret the operands as signed, then check for overflow.
        let of := dst1.toInt64.toInt - src1.toInt64.toInt >= 2^64
        -- ZF: result equals 0?
        let zf := res = 0
        set_reg_or_mem s dst (UInt64.ofInt res) (fun s  =>
        ret { s with flags := { zf, of, cf }})))

  | _ => throw s!"unsupported non-control instruction {repr i}"

def jump_if [Throw α] (s: MachineState) (b: Bool) (rip: Nat) (ret: MachineState → α): α :=
  if b then
    ret { s with rip }
  else
    ret (next s)


def ctrl [Throw α] (s: MachineState) (lookup: Label → (Nat → α) → α) (i: Instr) (ret: MachineState → α): α :=
  match i with
  | .jmp l =>
      lookup l (fun rip =>
      jump_if s True rip ret)
  | .jnz l =>
      lookup l (fun rip =>
      jump_if s (!s.flags.zf) rip ret)
  | .jz l =>
      lookup l (fun rip =>
      jump_if s s.flags.zf rip ret)
  | _ => throw s!"unsupported control instruction {repr i}"

abbrev Program := List (Option Label × Instr)

def lookup [Throw α] (p: Program) (l: Label) (ret: Nat → α): α :=
  match p.findIdx? (fun (l', _) => l' = .some l) with
  | .some rip => ret rip
  | .none => throw s!"Invalid label: {repr l}"

def fetch [Throw α] (p: Program) (s: MachineState) (ret: (Option Label × Instr) → α): α :=
  match p[s.rip]? with
  | .some ins => ret ins
  | .none => throw "Impossible: PC outside of program bounds"

def eval1 [m: Throw α] (p: Program) (s: MachineState) (ret: MachineState → α): α :=
  fetch p s (fun (_, i) =>
    if i.is_ctrl then
      ctrl s (lookup p) i ret
    else
      strt1 s i (fun s =>
      ret (next s)))

def eval (p: Program) (s: MachineState): Option MachineState := do
  let s ← (eval1 (m:={ throw _ := Option.none }) p s) (fun s => .some s)
  eval p s
partial_fixpoint

def step1 (p: Program) (s: MachineState) (post: _) :=
  eval1 (m:={ throw _ := False }) p s post

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
        <;> assumption -- Q: why does `grind` not work here?

theorem eventually_weaken (program: Program) (p q: Post)
  (h: forall s, p s → q s):
    eventually program p initial → eventually program q initial
  := by
    intro hp
    induction ih: hp -- Q: why does this not work with `induction ... with`?
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

-- Useful to debug the step_by tactic
example: step1 p1 {} (fun s => s.regs.rax = 1) := by
  simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,set_reg_or_mem,next]
  simp [MachineState.setReg,Registers.set]

def p11: Program := [
  (.none, .mov (.reg .rbx) (.imm 2)),    -- rbx := 2
  (.none, .adcx (.reg .rax) (.reg .rbx)) -- rax := rax + rbx
]

example (s_old: MachineState) (pre: s_old.rip = 0 ∧ (s_old.getReg .rax).toNat + 2 < 2^64):
    eventually p11 (fun s => (s.getReg .rax).toNat = (s_old.getReg .rax).toNat + 2) s_old
  := by
    rcases pre with ⟨ h_pre, h_bound ⟩
    apply step_cps
    simp [p11]
    delta step1 ExceptCpsT.runK eval1 fetch bind pure -- ExceptCpsT.instMonad.toBind.1
    rw [h_pre]
    delta List.findIdx? List.findIdx getElem? List.get?Internal
    --
    sorry

def p2: Program := [
  (.some "start", .mov (.reg .rax) (.imm 1)),
  (.none,         .jz "start"),
  (.none,         .mov (.reg .rax) (.imm 2)),
]

-- NOTES: why is the right way of doing this? Ideally, we would not ask to
-- simplify anything that is not an internal definition, because it is not
-- modular. Problematic things here include, e.g., List.findIdx? (what if the
-- user uses this very function in their post-condition?).
--
-- Something equivalent to `match goal with` might work. Alternatively, we could
-- have copies of definitions, e.g. `def my_findIdx := normalize List.findIdx?`.
-- TODO: determine how to do that in Lean.
--
-- Furthermore, it would be nice to be able to specify that reducing e.g. a
-- projector should only be done if the left-hand side is not a variable.
syntax "step_one" : tactic
macro_rules
  | `(tactic|step_one) =>
  `(tactic|
    simp [
      step1,Instr.is_ctrl,eval1,fetch,Option.except,ExceptCpsT.runK,bind,pure,
      -- works for calls to strt1
      strt1,eval_operand,eval_reg_or_mem,set_reg,set_reg_or_mem,MachineState.setReg,next,Registers.set,pure,bind,next,MachineState.getReg,Registers.get,
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
  (forall state k, k ≠ 0 → invariant k state → eventually prog (invariant (k - 1)) state) →
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

def p3_spec (s: MachineState): Nat := 2^(2^s.regs.rbx.toNat)

theorem p3_correct (initial: MachineState):
    p3_spec initial < 2^64 →
    initial.rip = 0 →
    eventually p3 (fun s => s.regs.rdx.toNat == p3_spec initial ∧ s.regs.rax == 0) initial :=
  by
    intros h_bounds h_rip
    simp [p3]
    -- First step sets rdx = 2
    apply step_cps
    step_one
    rw [h_rip]
    clear h_rip
    simp

    -- Loop invariant introduction
    apply reg_dec_loop p3 _ _ (fun i s => s.rip = 1 ∧ s.regs.rbx.toNat = i ∧ s.regs.rdx.toNat = 2^(2^(initial.regs.rbx.toNat - i))) initial.regs.rbx.toNat
    constructor
    . simp
    . constructor
      -- Invariant at index 0 ==> post
      . intros state inv
        rcases inv with ⟨ h_rip, h_rbx_zero, h_inv ⟩
        -- Step through a few program steps to "see" the jump and writing the
        -- sucess return value in rax
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
        rcases inv with ⟨ h_rip, h_rbx_is_k, h_inv ⟩

        simp [p3]
        apply step_cps
        step_one
        rw [h_rip]
        simp

        apply step_cps
        step_one
        have : (state.regs.rbx.toNat = 0) = False := by grind
        simp [this]

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
        . simp
          constructor
          . sorry
          . sorry
