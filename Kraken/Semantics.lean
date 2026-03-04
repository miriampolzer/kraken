/-
Kraken - x86_64 Assembly Interpreter Semantics

Core semantics for the assembly interpreter.
Compatible with Lean 4.22.0+.

For theorems, see Kraken/Theorems.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Std
import Lean.Elab.Tactic.Grind

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
-- Immediates: we use a single Int64 type since the parser already handles
-- sign-extension from AT&T syntax. The semantic value is always 64-bit signed.
| imm (v : Int64)                                        -- $42 (signed immediate)
| mem (base : Reg) (idx : Option Reg := .none) (scale : Nat := 1) (disp : Int := 0)
  -- Standard x86: base + idx*scale + disp. E.g. 8(%rsp) = disp 8, (%rsi,%r15,8) = idx .r15
  -- Per Intel SDM Vol. 2A Section 2.1.5 (SIB byte), valid scale values are 1, 2, 4, 8.
  -- The default scale is 1 (SIB SS bits = 00). Scale must be explicit in AT&T syntax when != 1.
deriving Repr, BEq

instance : Coe Reg Operand where coe := Operand.reg
instance : Coe Int64 Operand where coe := Operand.imm
attribute [coe] Operand.reg
attribute [coe] Operand.imm

abbrev Label := String

-- Condition codes for conditional jumps
inductive CondCode
| z    -- Zero (ZF=1)
| nz   -- Not Zero (ZF=0)
| b    -- Below/Carry (CF=1)
| ae   -- Above or Equal (CF=0)
| a    -- Above (CF=0 ∧ ZF=0)
| be   -- Below or Equal (CF=1 ∨ ZF=1)
deriving Repr, BEq, DecidableEq

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

  -- Move/Load (simplified: only 64-bit and 32-bit zero-extending needed for benchmarks)
  | mov  (dst src : Operand)                   -- movq/movabs: 64-bit move (imm if smaller, is sign-extended from 32-bit)
  | movl (dst src : Operand)                   -- movl: 32-bit move, ZERO-extends to 64-bit
  | lea  (dst : Reg) (src : Operand)           -- leaq: dst = effective address

  -- Bitwise
  | xor  (dst src : Operand)                   -- xorq: dst ^= src, clears CF/OF, sets ZF
  | and  (dst src : Operand)                   -- andq: dst &= src, clears CF/OF, sets ZF
  | or   (dst src : Operand)                   -- orq: dst |= src, clears CF/OF, sets ZF

  -- Compare (sets flags only)
  | cmp  (a b : Operand)                       -- cmpq: compute a - b, set flags

  -- Control flow (explicit jumps - core design of Kraken)
  -- Unconditional jump
  | jmp (target : Label)
  -- Conditional jump: jcc (condition code, target)
  -- Mapping from AT&T syntax to CondCode:
  --   AT&T    CondCode   Condition          Flags tested
  --   ----    --------   ---------          ------------
  --   jz      .z         Zero               ZF=1
  --   jnz     .nz        Not Zero           ZF=0
  --   je      .z         Equal (alias)      ZF=1
  --   jne     .nz        Not Equal (alias)  ZF=0
  --   jb      .b         Below (unsigned)   CF=1
  --   jae     .ae        Above/Equal        CF=0
  --   ja      .a         Above (unsigned)   CF=0 ∧ ZF=0
  --   jbe     .be        Below/Equal        CF=1 ∨ ZF=1
  | jcc (cc : CondCode) (target : Label)
  deriving Repr

def Instr.is_ctrl
  | Instr.jmp _ | Instr.jcc _ _ => true
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

-- Sign-extension helpers: use standard integer type conversions
-- Strategy: truncate to input size → signed Int conversion → convert to UInt64
-- This avoids branching on sign bit and is more proof-friendly.

-- 8-bit sign extension: UInt64 → UInt8 → Int8 → Int → UInt64
@[simp] def sign_extend_8_to_64 (v : UInt64) : UInt64 :=
  let truncated : UInt8 := v.toUInt8
  let signed : Int := truncated.toInt8.toInt
  UInt64.ofInt signed

-- 16-bit sign extension: UInt64 → UInt16 → Int16 → Int → UInt64
@[simp] def sign_extend_16_to_64 (v : UInt64) : UInt64 :=
  let truncated : UInt16 := v.toUInt16
  let signed : Int := truncated.toInt16.toInt
  UInt64.ofInt signed

-- 32-bit sign extension: UInt64 → UInt32 → Int32 → Int → UInt64
@[simp] def sign_extend_32_to_64 (v : UInt64) : UInt64 :=
  let truncated : UInt32 := v.toUInt32
  let signed : Int := truncated.toInt32.toInt
  UInt64.ofInt signed

-- Zero-extension helpers: truncate to input size, then widen (unsigned)
-- Upper bits are implicitly zero when converting smaller unsigned to larger

@[simp] def zero_extend_8_to_64 (v : UInt64) : UInt64 := v.toUInt8.toUInt64
@[simp] def zero_extend_16_to_64 (v : UInt64) : UInt64 := v.toUInt16.toUInt64
@[simp] def zero_extend_32_to_64 (v : UInt64) : UInt64 := v.toUInt32.toUInt64

-- Partial register write helpers: merge new value into existing register
-- These preserve upper bits of dst and write lower bits from src
@[simp] def write_low_8 (dst src : UInt64) : UInt64 := (dst &&& 0xFFFFFFFFFFFFFF00) ||| zero_extend_8_to_64 src
@[simp] def write_low_16 (dst src : UInt64) : UInt64 := (dst &&& 0xFFFFFFFFFFFF0000) ||| zero_extend_16_to_64 src
-- movl zero-extends, so it's just zero_extend_32_to_64 (no preservation)

-- Convert Int64 immediate to UInt64
@[simp] def eval_imm (v : Int64) : UInt64 := v.toUInt64




-- Compute effective address: base + idx*scale + disp
def effective_addr [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .mem base idx scale disp =>
    let idxVal := match idx with | .some r => s.getReg r | .none => 0
    ret ((s.getReg base) + idxVal * scale.toUInt64 + UInt64.ofInt disp)
  | _ => throw "effective_addr called on non-memory operand"

def eval_operand [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .imm v => ret (eval_imm v)
  | .mem _ _ _ _ => effective_addr s o (fun addr => s.readMem addr ret)

def eval_reg_or_mem [Throw α] (s : MachineState) (o : Operand) (ret: UInt64 → α): α :=
  match o with
  | .reg r => ret (s.getReg r)
  | .mem _ _ _ _ => effective_addr s o (fun addr => s.readMem addr ret)
  | .imm _ => throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg_or_mem [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ _ _ =>
      effective_addr s o (fun addr => s.writeMem addr v ret)
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"

def set_reg [Throw α] (s: MachineState) (o: Operand) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r =>
      ret (s.setReg r v)
  | .mem _ _ _ _
  | .imm _ =>
      throw "Ill-formed instruction (rip={repr s.rip})"


def next (s: MachineState): MachineState := { s with rip := s.rip + 1 }

-- Signed overflow detection for addition with carry: compare unbounded Int sum to truncated Int64 result
-- Overflow occurs iff the unbounded sum differs from the signed interpretation of the truncated result
-- Per Intel SDM, OF reflects the full operation including carry-in
def add_overflow_with_carry (a b : UInt64) (carry_in : Nat) : Bool :=
  let unbounded := a.toInt64.toInt + b.toInt64.toInt + carry_in
  let result := UInt64.ofNat (a.toNat + b.toNat + carry_in)
  let truncated := result.toInt64.toInt
  unbounded != truncated

-- Addition with carry: dst + src + carry_in
-- Returns (result, zf, cf, of)
def add_with_carry (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  let unbounded := dst.toNat + src.toNat + carry_in
  let result64 := UInt64.ofNat unbounded
  let zf := result64 == 0
  let cf := unbounded >= 2^64  -- Carry if result doesn't fit in 64 bits
  let of := add_overflow_with_carry dst src carry_in
  (result64, zf, cf, of)

-- Signed overflow detection for subtraction with borrow: compare unbounded Int diff to truncated Int64 result
-- Per Intel SDM, OF reflects the full operation including borrow-in
def sub_overflow_with_borrow (a b : UInt64) (borrow_in : Nat) : Bool :=
  let unbounded := a.toInt64.toInt - b.toInt64.toInt - borrow_in
  let result := UInt64.ofInt (a.toNat - b.toNat - borrow_in)
  let truncated := result.toInt64.toInt
  unbounded != truncated

-- Subtraction with borrow: dst - src - carry_in
-- Returns (result, zf, cf, of)
def sub_with_borrow (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  -- Use Int to handle negative results correctly (Nat subtraction saturates to 0)
  let unbounded : Int := dst.toNat - src.toNat - carry_in
  let result64 := UInt64.ofInt unbounded
  let zf := result64 == 0
  let cf := src.toNat + carry_in > dst.toNat  -- Borrow if src+carry > dst (unsigned)
  let of := sub_overflow_with_borrow dst src carry_in
  (result64, zf, cf, of)

-- Backward-compatible aliases (used in step_one tactic simp set and CMP instruction)
def add_overflow (a b : UInt64) : Bool := add_overflow_with_carry a b 0
def sub_overflow (a b : UInt64) : Bool := sub_overflow_with_borrow a b 0

-- This function intentionally does not increase the pc, callers will increase
-- it (always by 1).
-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def strt1 [Throw α] (s : MachineState) (i : Instr) (ret: MachineState → α): α :=
  match i with
  | .mov dst src =>
      -- 64-bit move (movq/movabs): direct copy of evaluated value
      -- For immediates, Int64.toUInt64 already gives the correct 64-bit value
      eval_operand s src (fun val =>
      set_reg_or_mem s dst val ret)

  | .movl dst src =>
      -- 32-bit move: ZERO-extends to 64-bit (clears upper 32 bits)
      eval_operand s src (fun val =>
      set_reg_or_mem s dst (zero_extend_32_to_64 val) ret)

  | .add dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := add_with_carry dst_v src_v 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adc dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := add_with_carry dst_v src_v s.flags.cf.toNat
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

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

  | .sub dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := sub_with_borrow dst_v src_v 0
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .sbb dst src =>
      -- Per Intel SDM: OF, SF, ZF, AF, PF, and CF flags are set according to the result
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let (result64, zf, cf, of) := sub_with_borrow dst_v src_v s.flags.cf.toNat
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .mul src =>
      -- mulq: rdx:rax = rax * src
      eval_reg_or_mem s src (fun src_v =>
      let rax_v := s.getReg .rax
      let result := rax_v.toNat * src_v.toNat
      let lo := UInt64.ofNat result
      let hi := UInt64.ofNat (result >>> 64)
      let s := s.setReg .rax lo
      let s := s.setReg .rdx hi
      -- mul sets OF and CF if high half is non-zero
      let cf := hi != 0
      let of := hi != 0
      ret { s with flags := { s.flags with cf, of }})

  | .mulx hi lo src1 =>
      eval_reg_or_mem s src1 (fun src1_v  =>
      let src2_v := s.getReg .rdx
      let result := src1_v.toNat * src2_v.toNat
      -- Semantics say that if hi and lo are aliased, the value written is hi
      set_reg s lo (UInt64.ofNat result) (fun s  =>
      set_reg s hi (UInt64.ofNat (result >>> 64)) ret))

  | .imul dst src =>
      -- Per Intel SDM: IMUL performs SIGNED multiplication
      -- Two-operand form: DEST := truncate(DEST × SRC) (signed)
      -- OF/CF set when signed result doesn't fit in destination size
      eval_reg_or_mem s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v.toInt64.toInt * src_v.toInt64.toInt
      let result64 := UInt64.ofInt result
      -- OF/CF set if sign-extended truncated result differs from full result
      let signExtended := result64.toInt64.toInt
      let overflow := result != signExtended
      set_reg_or_mem s dst result64 (fun s =>
      ret { s with flags := { s.flags with cf := overflow, of := overflow }})))

  | .neg dst =>
      -- Per Intel SDM: CF set unless operand is 0; OF set according to result
      -- OF is set when negating the most negative value (INT64_MIN)
      eval_reg_or_mem s dst (fun dst_v =>
      -- Two's complement negation: negate via Int64 to ensure correct wrapping
      let result := (-(dst_v.toInt64)).toUInt64
      let zf := result == 0
      let cf := dst_v != 0  -- CF is set unless operand is 0
      let of := dst_v == 0x8000000000000000  -- OF set when negating INT64_MIN
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, cf, of }}))

  | .dec dst =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v - 1
      let zf := result == 0
      -- Signed overflow occurs when decrementing INT64_MIN (produces positive result)
      let of := dst_v == 0x8000000000000000
      -- dec does NOT affect CF
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { s.flags with zf, of }}))

  | .lea dst src =>
      -- lea computes effective address, doesn't access memory
      effective_addr s src (fun addr => ret (s.setReg dst addr))

  | .xor dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v ^^^ src_v
      let zf := result == 0
      -- xor clears CF and OF
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .and dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v &&& src_v
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .or dst src =>
      eval_operand s src (fun src_v =>
      eval_reg_or_mem s dst (fun dst_v =>
      let result := dst_v ||| src_v
      let zf := result == 0
      set_reg_or_mem s dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .cmp a b =>
      eval_reg_or_mem s a (fun a_v =>
      eval_operand s b (fun b_v =>
      let res := (Int.ofNat a_v.toNat) - (Int.ofNat b_v.toNat)
      let cf := res < 0
      let zf := res == 0
      let of := sub_overflow a_v b_v
      ret { s with flags := { zf, of, cf }}))

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
  | .jcc cc l =>
      lookup l (fun rip =>
      let cond := match cc with
        | .z  => s.flags.zf           -- Zero: ZF=1
        | .nz => !s.flags.zf          -- Not Zero: ZF=0
        | .b  => s.flags.cf           -- Below: CF=1
        | .ae => !s.flags.cf          -- Above/Equal: CF=0
        | .a  => !s.flags.cf && !s.flags.zf  -- Above: CF=0 ∧ ZF=0
        | .be => s.flags.cf || s.flags.zf    -- Below/Equal: CF=1 ∨ ZF=1
      jump_if s cond rip ret)
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
