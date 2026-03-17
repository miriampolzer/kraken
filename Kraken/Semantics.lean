/-
Kraken - x86_64 Assembly Interpreter Semantics

Core semantics for the assembly interpreter.
Compatible with Lean 4.22.0+.

For theorems, see Kraken/Theorems.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Std
import Lean.Elab.Tactic.Grind

-- ============================================================================
-- Width Type
-- ============================================================================

/-- Operand width for multi-width instructions. -/
inductive Width | W8 | W16 | W32 | W64
  deriving Repr, BEq, DecidableEq

def Width.toNat : Width → Nat
  | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64

def Width.toBytes : Width → UInt64
  | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8

def Width.toUInt64 (w: Width): UInt64 :=
  w.toNat.toUInt64

/-- Mask for extracting the low bits of the specified width. -/
def Width.toMask : Width → UInt64
  | W8  => 0xFF
  | W16 => 0xFFFF
  | W32 => 0xFFFFFFFF
  | W64 => 0xFFFFFFFFFFFFFFFF

/-- A shift mask -- see https://www.felixcloutier.com/x86/sal:sar:shl:shr
    "The count is masked to 5 bits (or 6 bits with a 64-bit operand)" -/
def Width.toShiftMask : Width → UInt64
  | W64 => 0x1f
  | _ => 0x0f

-- ============================================================================
-- Registers Enumeration (extended with aliases)
-- ============================================================================

/-- x86-64 registers including aliased sub-registers.
    - 64-bit: rax, rbx, ..., r15
    - 32-bit: eax, ebx, ..., r15d (zero-extend on write per Intel SDM)
    - 16-bit: ax, bx, ..., r15w (preserve upper bits on write)
    - 8-bit low: al, bl, ..., r15b (preserve upper bits on write)
 -/
inductive Reg
  -- 64-bit registers
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  -- 32-bit aliases (zero-extend to 64-bit on write)
  | eax | ebx | ecx | edx
  | esi | edi | esp | ebp
  | r8d | r9d | r10d | r11d
  | r12d | r13d | r14d | r15d
  -- 16-bit aliases (preserve upper 48 bits on write)
  | ax | bx | cx | dx
  | si | di | sp | bp
  | r8w | r9w | r10w | r11w
  | r12w | r13w | r14w | r15w
  -- 8-bit low aliases (preserve upper 56 bits on write)
  | al | bl | cl | dl
  | sil | dil | spl | bpl
  | r8b | r9b | r10b | r11b
  | r12b | r13b | r14b | r15b
  deriving Repr, BEq, DecidableEq

/-- Get the width of a register. -/
@[simp] def Reg.width : Reg → Width
  | rax | rbx | rcx | rdx | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15 => .W64
  | eax | ebx | ecx | edx | esi | edi | esp | ebp
  | r8d | r9d | r10d | r11d | r12d | r13d | r14d | r15d => .W32
  | ax | bx | cx | dx | si | di | sp | bp
  | r8w | r9w | r10w | r11w | r12w | r13w | r14w | r15w => .W16
  | al | bl | cl | dl | sil | dil | spl | bpl
  | r8b | r9b | r10b | r11b | r12b | r13b | r14b | r15b => .W8

@[simp] def Reg.IsBase : Reg → Prop
  | rax | rbx | rcx | rdx | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15 => True
  | _ => False

/-- One of the 16 base registers. We adopt a refinement here to avoid having to
  deal with error cases and requiring [Throw α] on a lot of our specifications -/
abbrev BaseReg := { r: Reg // r.IsBase }

/-- Get the 64-bit base register for any alias, along with a proof witness that
  it is indeed one of the 16 base registers. -/
def Reg.base : Reg → BaseReg
  | rax | eax | ax | al => ⟨ .rax, by simp ⟩
  | rbx | ebx | bx | bl => ⟨ .rbx, by simp ⟩
  | rcx | ecx | cx | cl => ⟨ .rcx, by simp ⟩
  | rdx | edx | dx | dl => ⟨ .rdx, by simp ⟩
  | rsi | esi | si | sil => ⟨ .rsi, by simp ⟩
  | rdi | edi | di | dil => ⟨ .rdi, by simp ⟩
  | rsp | esp | sp | spl => ⟨ .rsp, by simp ⟩
  | rbp | ebp | bp | bpl => ⟨ .rbp, by simp ⟩
  | r8  | r8d  | r8w  | r8b  => ⟨ .r8, by simp ⟩
  | r9  | r9d  | r9w  | r9b  => ⟨ .r9, by simp ⟩
  | r10 | r10d | r10w | r10b => ⟨ .r10, by simp ⟩
  | r11 | r11d | r11w | r11b => ⟨ .r11, by simp ⟩
  | r12 | r12d | r12w | r12b => ⟨ .r12, by simp ⟩
  | r13 | r13d | r13w | r13b => ⟨ .r13, by simp ⟩
  | r14 | r14d | r14w | r14b => ⟨ .r14, by simp ⟩
  | r15 | r15d | r15w | r15b => ⟨ .r15, by simp ⟩

def BaseReg.shrink64 (self: BaseReg) (w: Width): Reg :=
  let ⟨ self, _ ⟩ := self
  match self, w with
  | .rax, .W64 => .rax
  | .rax, .W32 => .eax
  | .rax, .W16 =>  .ax
  | .rax, .W8  =>  .al

  | .rbx, .W64 => .rbx
  | .rbx, .W32 => .ebx
  | .rbx, .W16 =>  .bx
  | .rbx, .W8  =>  .bl

  | .rcx, .W64 => .rcx
  | .rcx, .W32 => .ecx
  | .rcx, .W16 =>  .cx
  | .rcx, .W8  =>  .cl

  | .rdx, .W64 => .rdx
  | .rdx, .W32 => .edx
  | .rdx, .W16 =>  .dx
  | .rdx, .W8  =>  .dl

  | .rsi, .W64 => .rsi
  | .rsi, .W32 => .esi
  | .rsi, .W16 =>  .si
  | .rsi, .W8  =>  .sil

  | .rdi, .W64 => .rdi
  | .rdi, .W32 => .edi
  | .rdi, .W16 =>  .di
  | .rdi, .W8  =>  .dil

  | .rsp, .W64 => .rsp
  | .rsp, .W32 => .esp
  | .rsp, .W16 =>  .sp
  | .rsp, .W8  =>  .spl

  | .rbp, .W64 => .rbp
  | .rbp, .W32 => .ebp
  | .rbp, .W16 =>  .bp
  | .rbp, .W8  =>  .bpl

  | .r8, .W64 => .r8
  | .r8, .W32 => .r8d
  | .r8, .W16 => .r8w
  | .r8, .W8  => .r8b

  | .r9, .W64 => .r9
  | .r9, .W32 => .r9d
  | .r9, .W16 => .r9w
  | .r9, .W8  => .r9b

  | .r10, .W64 => .r10
  | .r10, .W32 => .r10d
  | .r10, .W16 => .r10w
  | .r10, .W8  => .r10b

  | .r11, .W64 => .r11
  | .r11, .W32 => .r11d
  | .r11, .W16 => .r11w
  | .r11, .W8  => .r11b

  | .r12, .W64 => .r12
  | .r12, .W32 => .r12d
  | .r12, .W16 => .r12w
  | .r12, .W8  => .r12b

  | .r13, .W64 => .r13
  | .r13, .W32 => .r13d
  | .r13, .W16 => .r13w
  | .r13, .W8  => .r13b

  | .r14, .W64 => .r14
  | .r14, .W32 => .r14d
  | .r14, .W16 => .r14w
  | .r14, .W8  => .r14b

  | .r15, .W64 => .r15
  | .r15, .W32 => .r15d
  | .r15, .W16 => .r15w
  | .r15, .W8  => .r15b

def Reg.shrink (self: Reg) (w: Width): Reg :=
  self.base.shrink64 w

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
abbrev Label := String
abbrev Heap := Std.ExtHashMap Address Word

instance : Repr Heap where
  reprPrec _ _ := "<opaque memory>"

abbrev Position := Label × Nat
def Position.Label (l : Label) : Position := (l, 0)
instance : Coe Label Position where coe := Position.Label
attribute [coe] Position.Label

class Layout where
  layout: Position → Address
def layout [inst: Layout] := inst.layout
def label [inst: Layout] l := inst.layout (l, 0)

-- Machine State
structure MachineState where
  regs : Registers := {}
  flags : Flags := {}
  heap : Heap := ∅
deriving Repr


inductive Constexpr
| Label (_ : Label)
| Int (_ : Int)
-- Careful adding operations here! Need to match overflow behavior of all
-- assemblers we want compatibility with. We assume oversized literals error.
deriving Repr, BEq
instance : Coe Label Constexpr where coe := Constexpr.Label
instance : Coe Int Constexpr where coe := Constexpr.Int
attribute [coe] Constexpr.Label
attribute [coe] Constexpr.Int

-- Operands (extended with indexed memory modes for MontMul)
-- Memory operands use WORD offsets (multiplied by 8 in code gen) for alignment

/- We generally operate under the assumption that the width of an operation can
   be deduced from its operands, which allows us to keep a single inductive
   constructor for many variants. For instance, `mov %eax $0` is the r/32 i/32
   variant from https://www.felixcloutier.com/x86/mov. However, looking at `mov
   offset(%rax, %rbx, 4) $0`, we do not know whether we intend to write a byte
   or a 64-bit word. That is, we know that the *address size* is 64-bit [1], but
   we are missing the operand size. For that reason, and in keeping with the
   Intel syntax [2], we add an additional disambiguator to memory operands to
   capture the *operand size*. In most cases, the width of the *destination*
   operand determines which variant of the instruction we use. Some instructions
   like `mulx` have special cases. Note that this is in spirit identical to what
   AT&T syntax does [3], except the disambiguator is a one-letter suffix
   appended to the instruction code. 
  
   [1] https://wiki.osdev.org/X86-64_Instruction_Encoding#Operand-size_and_address-size_override_prefix
   [2] https://en.wikipedia.org/wiki/X86_assembly_language#Syntax
   [3] https://sourceware.org/binutils/docs/as/i386_002dMnemonics.html
-/
structure MemoryOperand where
  width : Width
  base : Reg
  idx : Option Reg := .none
  scale : Width := .W8
  disp : Constexpr := .Int 0
  -- Standard x86: base + idx*scale + disp. E.g. 8(%rsp) = disp 8, (%rsi,%r15,8) = idx .r15
  -- Per Intel SDM Vol. 2A Section 2.1.5 (SIB byte), valid scale values are 1, 2, 4, 8.
  -- The default scale is 1 (SIB SS bits = 00). Scale must be explicit in AT&T syntax when != 1.
deriving Repr, BEq

inductive RegOrMem | reg (r : Reg) | mem (_ : MemoryOperand)
deriving Repr, BEq

instance : Coe MemoryOperand RegOrMem where coe := RegOrMem.mem
attribute [coe] RegOrMem.mem
instance : Coe Reg RegOrMem where coe := RegOrMem.reg
attribute [coe] RegOrMem.reg

def RegOrMem.width : RegOrMem → Width
| .reg r => r.width
| .mem o => o.width

inductive Operand | RegOrMem (_ : RegOrMem) | imm (v : Constexpr)
deriving Repr, BEq

abbrev Dst := RegOrMem

instance : Coe RegOrMem Operand where coe := Operand.RegOrMem
attribute [coe] Operand.RegOrMem
instance : Coe Constexpr Operand where coe := Operand.imm
attribute [coe] Operand.imm

-- There is one case where the variant of instruction cannot be determined --
-- pushing an immediate to the stack. For that case, we annotate the immediate
-- with a width.
inductive SrcAndWidth
| typed (o: Operand) (extra: match o with | Operand.imm _ => Width | _ => Unit)

instance : Repr SrcAndWidth where
  reprPrec o n :=
    match o with
    | .typed (.imm i) w =>
        let w: Width := w
        Repr.reprPrec i n ++ "/" ++ Repr.reprPrec w n
    | .typed o _ => Repr.reprPrec o n

-- Condition codes for conditional jumps
inductive CondCode
| z    -- Zero (ZF=1)
| nz   -- Not Zero (ZF=0)
| c    -- Below/Carry (CF=1)
| nc   -- Above or Equal (CF=0)
| a    -- Above (CF=0 ∧ ZF=0)
| be   -- Below or Equal (CF=1 ∨ ZF=1)
deriving Repr, BEq, DecidableEq
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

-- Instructions (extended for scalar crypto benchmarks)
inductive Instr
  -- Arithmetic (64-bit)
  | add  (_ : Dst) (src : Operand)                   -- addq: dst += src, sets CF, ZF, OF
  | adc  (_ : Dst) (src : Operand)                   -- adcq: dst += src + CF, sets CF, ZF
  | adcx (_ : Reg) (src : Operand)                   -- adcxq: dst += src + CF, only affects CF (ADX)
  | adox (dst : Reg) (src : Operand)                 -- adoxq: dst += src + OF, only affects OF (ADX)
  | sub  (_ : Dst) (src : Operand)                   -- subq: dst -= src, sets CF, ZF, OF
  | sbb  (_ : Dst) (src : Operand)                   -- sbbq: dst -= src + CF, sets CF, ZF
  | mul  (src : RegOrMem)                            -- mulq: rdx:rax = rax * src
  | mulx (hi lo : Reg) (src : RegOrMem)              -- mulxq: hi:lo = rdx * src (BMI2, no flags)
  | imul (_ : Dst) (src : Operand)                   -- imulq: dst *= src (truncated, sets OF/CF)
  | neg  (_ : Dst)                                   -- negq: dst = -dst, sets CF, ZF, OF
  | dec  (_ : Dst)                                   -- decq: dst--, sets ZF (not CF!)

  -- Move/Load
  | mov   (_ : Dst) (src : Operand)                  -- movq/movabs: 64-bit move
  | movzx (_ : Dst) (src : Operand)                  -- movzbl: byte to 32-bit zero-extend (then to 64)
  | lea   (_ : Reg) (src : MemoryOperand)            -- leaq: dst = effective address

  -- Shifts (64-bit)
  | shl  (_ : Dst) (count : Operand)                 -- shlq: logical shift left
  | shr  (_ : Dst) (count : Operand)                 -- shrq: logical shift right
  | sar  (_ : Dst) (count : Operand)                 -- sarq: arithmetic shift right
  | shld (_ : Dst) (src count : Operand)             -- shldq: double-precision shift left
  | shrd (_ : Dst) (src count : Operand)             -- shrdq: double-precision shift right

  -- Rotates (64-bit)
  | rol  (_ : Dst) (count : Operand)                 -- rolq: rotate left
  | ror  (_ : Dst) (count : Operand)                 -- rorq: rotate right

  -- Byte swap
  | bswap  (dst : Reg)                               -- bswapq: 64-bit byte swap

  -- Bitwise (64-bit)
  | xor  (_ : Dst) (src : Operand)                   -- xorq: dst ^= src, clears CF/OF, sets ZF
  | and  (_ : Dst) (src : Operand)                   -- andq: dst &= src, clears CF/OF, sets ZF
  | or   (_ : Dst) (src : Operand)                   -- orq: dst |= src, clears CF/OF, sets ZF

  -- Test (AND but discard result, set flags)
  | test (a b : Operand)                             -- testq: a AND b, set flags

  -- Compare (sets flags only)
  | cmp  (a : RegOrMem) (b : Operand)                -- cmpq: compute a - b, set flags

  -- Stack operations. Because `push` may take an immediate, we have to take a
  -- width.
  | push (src : SrcAndWidth)                         -- pushq: RSP -= N, [RSP] = src
  | pop  (_ : Dst)                                   -- popq: dst = [RSP], RSP += N

  -- Set byte on condition
  | setcc (_ : CondCode) (_ : Dst)                   -- setCC: set byte to condition code
  | cmovcc (_ : CondCode) (_ : Reg) (src : RegOrMem) -- cmovcq: move if condition satisfied

  -- Control flow
  | jmp (target : Label)                             -- Unconditional jump
  | ret                                              -- Return from function
  | jcc (cc : CondCode) (target : Label)
  deriving Repr

abbrev Program := List (Label × List Instr)

def Instr.is_ctrl
  | Instr.jmp _ | Instr.jcc _ _ | Instr.ret => true
  | _ => false

-- ============================================================================
-- Register Access
-- ============================================================================

/-- Read low 8 bits. -/
@[simp] def mask8 (x : UInt64) : UInt64 := x &&& Width.W8.toMask

/-- Read low 16 bits. -/
@[simp] def mask16 (x : UInt64) : UInt64 := x &&& Width.W16.toMask

/-- Read low 32 bits. -/
@[simp] def mask32 (x : UInt64) : UInt64 := x &&& Width.W32.toMask

/-- Write to low 8 bits, preserving upper 56. -/
@[inline] def write8 (dst src : UInt64) : UInt64 :=
  (dst &&& ~~~Width.W8.toMask) ||| mask8 src

/-- Write to low 16 bits, preserving upper 48. -/
@[inline] def write16 (dst src : UInt64) : UInt64 :=
  (dst &&& ~~~Width.W16.toMask) ||| mask16 src

def Registers.get64 (regs: Registers) (r: BaseReg): UInt64 :=
  let ⟨ r, _ ⟩ := r
  match r with
  | .rax => regs.rax | .rbx => regs.rbx | .rcx => regs.rcx | .rdx => regs.rdx
  | .rsi => regs.rsi | .rdi => regs.rdi | .rsp => regs.rsp | .rbp => regs.rbp
  | .r8  => regs.r8  | .r9  => regs.r9  | .r10 => regs.r10 | .r11 => regs.r11
  | .r12 => regs.r12 | .r13 => regs.r13 | .r14 => regs.r14 | .r15 => regs.r15

/-- Get a register value with appropriate masking for aliased registers.
    Returns the value as seen through the register's width. -/
def Registers.get (regs : Registers) (r : Reg) : UInt64 :=
  let v := regs.get64 r.base
  match r.width with
  -- 64-bit registers: direct read
  | .W64 => v
  -- 32-bit: mask to 32 bits
  | .W32 => mask32 v
  -- 16-bit: mask to 16 bits
  | .W16 => mask16 v
  -- 8-bit: mask to 8 bits
  | .W8 => mask8 v

def Registers.set64 (regs : Registers) (r: BaseReg) (v: UInt64):
    Registers :=
  let ⟨ r, _ ⟩ := r
  match r with
  -- 64-bit registers: direct write
  | .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
  | .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
  | .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
  | .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
  | .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
  | .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
  | .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
  | .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

def w64_IsBase (r: Reg) (h: r.width = .W64): r.IsBase :=
  by
    cases r
    <;> simp at *

/-- Set a register value with appropriate aliasing behavior:
    - 64-bit: direct write
    - 32-bit: zero-extends to 64-bit (clears upper 32 bits) per Intel SDM
    - 16-bit: preserves upper 48 bits
    - 8-bit: preserves upper 56 bits -/
def Registers.set (regs : Registers) (r : Reg) (v : UInt64) : Registers :=
  match h: r.width with
  | .W64 => regs.set64 ⟨ r, w64_IsBase r h ⟩ v
  | .W32 => regs.set64 r.base (mask32 v)
  | .W16 => regs.set64 r.base (write16 (regs.get64 r.base) v)
  | .W8 => regs.set64 r.base (write8 (regs.get64 r.base) v)

def MachineState.getReg (s : MachineState) (r : Reg) : UInt64 :=
  s.regs.get r

def MachineState.setReg (s : MachineState) (r : Reg) (v : UInt64) : MachineState :=
  { s with regs := s.regs.set r v }

class Throw α where
  throw: String → α

def throw {α} [inst: Throw α] :=
  inst.throw

def MachineState.readMem [Throw α] (s : MachineState) (addr : Address) (width: Width) (ret: Word → α): α :=
  if addr % 8 != 0 then
    throw (s!"Out-of-bounds access")
  else
    match s.heap[addr]? with
    | .some v => ret (v &&& width.toMask) -- little-endian
    | .none => throw (s!"Memory read but not written to (addr={repr addr})")

def MachineState.writeMem [Throw α] (s : MachineState) (addr : Address) (w: Width) (val : Word) (ret: MachineState → α) : α :=
  if addr % 8 != 0 then
    throw s!"Out-of-bounds access"
  else if w != .W64 then
    throw s!"TODO: figure out what we do here"
  else
    ret { s with heap := s.heap.insert addr val }

-- We only track values held in the widest registers -- these are 64-bit, without any particular
-- intepretation, i.e., UInt64. However, for the computation of e.g. the overflow flag, one has to
-- intepret the value held in a potentially smaller register **as a signed integer**.
def UInt64.toIntWithWidth (self: UInt64) (w: Width): Int :=
  -- TODO: is there a more direct way of doing this?
  match w with
  | .W64 => self.toInt64.toInt
  | .W32 => (mask32 self).toNat.toInt32.toInt
  | .W16 => (mask16 self).toNat.toInt16.toInt
  | .W8 => (mask8 self).toNat.toInt8.toInt

def Int.clamp (self: Int) (w: Width): Int :=
  (UInt64.ofInt self).toIntWithWidth w


-- Overflow occurs iff the unbounded sum differs from the signed interpretation of the truncated result
-- Per Intel SDM, OF reflects the full operation including carry-in
def add_overflow_with_carry (w: Width) (a b : UInt64) (carry_in : Nat) : Bool :=
  let unbounded := a.toIntWithWidth w + b.toIntWithWidth w + carry_in
  let truncated := unbounded.clamp w
  unbounded != truncated

-- Addition with carry: dst + src + carry_in
-- Returns (result, zf, cf, of)
def add_with_carry (w: Width) (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  let unbounded := dst.toNat + src.toNat + carry_in
  let result64 := UInt64.ofNat unbounded
  let zf := result64 == 0
  let cf := unbounded >= 2^w.toNat  -- Carry if result doesn't fit in 64 bits
  let of := add_overflow_with_carry w dst src carry_in
  (result64, zf, cf, of)

-- Signed overflow detection for subtraction with borrow: compare unbounded Int diff to truncated Int64 result
-- Per Intel SDM, OF reflects the full operation including borrow-in
def sub_overflow_with_borrow (w: Width) (a b : UInt64) (borrow_in : Nat) : Bool :=
  let unbounded := a.toIntWithWidth w - b.toIntWithWidth w - borrow_in
  let truncated := unbounded.clamp w
  unbounded != truncated

-- Subtraction with borrow: dst - src - carry_in
-- Returns (result, zf, cf, of)
def sub_with_borrow (w: Width) (dst src : UInt64) (carry_in : Nat) : UInt64 × Bool × Bool × Bool :=
  -- Use Int to handle negative results correctly (Nat subtraction saturates to 0)
  let unbounded : Int := dst.toNat - src.toNat - carry_in
  let result64 := UInt64.ofInt unbounded
  let zf := result64 == 0
  -- CF set if overflow in unsigned, i.e.
  -- dst - src - carry_in < 0, which we rewrite to the form below (because Nat
  -- saturates down to 0)
  let cf := src.toNat + carry_in > dst.toNat
  let of := sub_overflow_with_borrow w dst src carry_in
  (result64, zf, cf, of)

-- Backward-compatible aliases (used in step_one tactic simp set and CMP instruction)
def add_overflow (w: Width) (a b : UInt64) : Bool := add_overflow_with_carry w a b 0
def sub_overflow (w: Width) (a b : UInt64) : Bool := sub_overflow_with_borrow w a b 0

def Reg.interp (r : Reg) (s : MachineState) (ret : UInt64 → α) :=
  ret (s.getReg r)

def CondCode.interp (cc : CondCode) (s : MachineState) : Bool :=
  match cc with
  | .z  => s.flags.zf           -- Zero: ZF=1
  | .nz => !s.flags.zf          -- Not Zero: ZF=0
  | .c  => s.flags.cf           -- Below: CF=1
  | .nc => !s.flags.cf          -- Above/Equal: CF=0
  | .a  => !s.flags.cf && !s.flags.zf  -- Above: CF=0 ∧ ZF=0
  | .be => s.flags.cf || s.flags.zf    -- Below/Equal: CF=1 ∨ ZF=1

section
variable [Layout]
def Constexpr.interp (ce : Constexpr) : Word :=
  match ce with
  | .Label l => label l
  | .Int i => UInt64.ofInt i

def MemoryOperand.addr (o : MemoryOperand) (s : MachineState) : Word :=
  let idxVal := match o.idx with | .some r => s.getReg r | .none => 0
  (s.getReg o.base) + idxVal * o.scale.toUInt64 + o.disp.interp

variable [Throw α]

def RegOrMem.interp (o : RegOrMem) (s : MachineState) (ret : UInt64 → α) :=
  match o with
  | .reg r => ret (s.getReg r)
  | .mem o => s.readMem (o.addr s) o.width ret

def Operand.interp (o : Operand) (s : MachineState) (ret : UInt64 → α) :=
  match o with
  | .RegOrMem rm => rm.interp s ret
  | .imm v => ret v.interp

def SrcAndWidth.width (o : SrcAndWidth) : Width :=
  match o with
  | .typed (.RegOrMem o) _ => o.width
  | .typed (.imm _) w => w

def SrcAndWidth.interp (o: SrcAndWidth) (s: MachineState) (ret: UInt64 → α): α :=
  match o with
  | .typed o _ => o.interp s ret

def MachineState.set (s: MachineState) (o: Dst) (v: Word) (ret: MachineState → α): α :=
  match o with
  | .reg r => ret (s.setReg r v)
  | .mem o => s.writeMem (o.addr s) o.width v ret


-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def x64 [Throw α] (s : MachineState) (i : Instr) (jmp : MachineState → Position → α) (ret : MachineState → α): α :=
  match i with
  | .mov dst src =>
      -- If we leave aside segment-related operations, MOV is homogenous (i.e.
      -- src and dst have the same width). The only case that performs
      -- sign-extension is when dst = 64-bit register, and src = 32-bit
      -- immediate, in which case Operand.interp takes care of sign-extending.
      src.interp s (fun val =>
      s.set dst val ret)

  | .movzx dst src =>
      -- Here, zero-extension happens inside src.interp which returns UInt64.
      src.interp s (fun val =>
      s.set dst val ret)

  | .add dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let (result64, zf, cf, of) := add_with_carry dst.width dst_v src_v 0
      s.set dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adc dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let (result64, zf, cf, of) := add_with_carry dst.width dst_v src_v s.flags.cf.toNat
      s.set dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .adcx dst src =>
      -- Relying on ASM syntax here to enforce that w == _w
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let result := src_v.toNat + dst_v.toNat + s.flags.cf.toNat
      let carry := result >>> dst.width.toNat
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with cf := carry != 0 }}
      ret (s.setReg dst result)))

  | .adox dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      -- TODO: figure out how to make sure that this let-binding does not get
      -- inlined, *unless* the right-hand side can be computed to a constant
      let result := src_v.toNat + dst_v.toNat + s.flags.of.toNat
      let carry := result >>> dst.width.toNat
      let result := UInt64.ofNat result
      let s := { s with flags := { s.flags with of := carry != 0 }}
      ret (s.setReg dst result)))

  | .sub dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let (result64, zf, cf, of) := sub_with_borrow dst.width dst_v src_v 0
      s.set dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .sbb dst src =>
      -- Per Intel SDM: OF, SF, ZF, AF, PF, and CF flags are set according to the result
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let (result64, zf, cf, of) := sub_with_borrow dst.width dst_v src_v s.flags.cf.toNat
      s.set dst result64 (fun s =>
      ret { s with flags := { zf, of, cf }})))

  | .mul src =>
      let w := src.width
      src.interp s (fun src_v =>
      let rax_v := s.getReg (Reg.shrink .rax w)
      let result := rax_v.toNat * src_v.toNat
      if w != .W8 then
        let lo := (UInt64.ofNat result) &&& w.toMask
        let hi := UInt64.ofNat (result >>> w.toNat)
        let r_lo := Reg.shrink .rax w
        let r_hi := Reg.shrink .rdx w
        let s := s.setReg r_lo lo
        let s := s.setReg r_hi hi
        -- mul sets OF and CF if high half is non-zero
        let cf := hi != 0
        let of := hi != 0
        ret { s with flags := { s.flags with cf, of }}
      else
        let cf := result &&& 0xFF00 != 0
        let of := result &&& 0xFF00 != 0
        let s := s.setReg .ax (UInt64.ofNat result)
        ret { s with flags := { s.flags with cf, of }}
      )

  | .mulx r_hi r_lo src1 =>
      let w := r_hi.width
      src1.interp s (fun src1_v =>
      let src2_v := s.getReg (Reg.shrink .rdx w)
      let result := src1_v.toNat * src2_v.toNat
      -- Semantics say that if hi and lo are aliased, the value written is hi
      let s := s.setReg (r_lo.shrink w) (UInt64.ofNat result)
      let s := s.setReg (r_hi.shrink w) (UInt64.ofNat (result >>> w.toNat))
      ret s)

  | .imul dst src =>
      -- imulq (64-bit only): Two-operand form DEST := truncate(DEST × SRC) (signed)
      -- Note: Other widths (imulb/imulw/imull) would need different truncation/sign-extension.
      -- The parser validates that operands are 64-bit. See: https://www.felixcloutier.com/x86/imul
      -- OF/CF set when signed result doesn't fit in destination size
      let w := dst.width
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let result := dst_v.toIntWithWidth w * src_v.toIntWithWidth w
      let result64 := UInt64.ofInt result
      -- OF/CF set if sign-extended truncated result differs from full result
      let overflow := result != result.clamp w
      s.set dst result64 (fun s =>
      ret { s with flags := { s.flags with cf := overflow, of := overflow }})))

  | .neg dst =>
      -- Per Intel SDM: CF set unless operand is 0; OF set according to result
      -- OF is set when negating the most negative value (INT64_MIN)
      dst.interp s (fun dst_v =>
      -- Two's complement negation: negate via IntXX to ensure correct wrapping
      let result := UInt64.ofInt (-(dst_v.toIntWithWidth dst.width))
      let zf := result == 0
      let cf := dst_v != 0  -- CF is set unless operand is 0
      let of := dst_v == result &&& dst.width.toMask -- OF set when negating INT64_MIN, i.e. when - is ineffective
      s.set dst result (fun s =>
      ret { s with flags := { s.flags with zf, cf, of }}))

  | .dec dst =>
      dst.interp s (fun dst_v =>
      -- DEC wraparounds, presumably like SUB
      let result := dst_v.toIntWithWidth dst.width - 1
      let result64 := UInt64.ofInt result
      let zf := result == 0
      -- Signed overflow occurs when decrementing INT64_MIN (produces positive result)
      let of := sub_overflow dst.width dst_v 1
      -- dec does NOT affect CF
      s.set dst result64 (fun s =>
      ret { s with flags := { s.flags with zf, of }}))

  | .lea dst src =>
      ret (s.setReg dst (src.addr s))


  | .xor dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let result := dst_v ^^^ src_v
      let zf := result == 0
      -- xor clears CF and OF
      s.set dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .and dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let result := dst_v &&& src_v
      let zf := result == 0
      s.set dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .or dst src =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let result := dst_v ||| src_v
      let zf := result == 0
      s.set dst result (fun s =>
      ret { s with flags := { zf, of := false, cf := false }})))

  | .cmp a b =>
      a.interp s (fun a_v =>
      b.interp s (fun b_v =>
      let (_, zf, cf, of) := sub_with_borrow a.width a_v b_v 0
      ret { s with flags := { zf, of, cf }}))

  -- ============================================================================
  -- Shift instructions
  -- ============================================================================

  | .shl dst count =>
      count.interp s (fun cnt =>
      dst.interp s (fun dst_v =>
      let result := dst_v <<< (cnt &&& dst.width.toShiftMask)
      let zf := result == 0
      -- BUG: define CF, OF for all shift operations
      s.set dst result (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .shr dst count =>
      count.interp s (fun cnt =>
      dst.interp s (fun dst_v =>
      let cnt_masked := cnt &&& dst.width.toShiftMask
      let result := dst_v >>> cnt_masked
      let zf := result == 0
      s.set dst result (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .sar dst count =>
      -- Arithmetic right shift (sign-extending)
      count.interp s (fun cnt =>
      dst.interp s (fun dst_v =>
      let cnt_masked := cnt &&& dst.width.toShiftMask
      let result := (dst_v.toIntWithWidth dst.width >>> cnt_masked.toNat).clamp dst.width
      let zf := result == 0
      s.set dst (UInt64.ofInt result) (fun s =>
      ret { s with flags := { s.flags with zf }})))

  | .shld dst src count =>
      -- Double-precision shift left: shift dst left by count, fill low bits from src high bits
      count.interp s (fun cnt =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let cnt_masked := cnt &&& dst.width.toShiftMask
      let result := if cnt_masked == 0 then dst_v
                    else (dst_v <<< cnt_masked) ||| (src_v >>> (dst.width.toUInt64 - cnt_masked))
      s.set dst result ret)))

  | .shrd dst src count =>
      -- Double-precision shift right: shift dst right by count, fill high bits from src low bits
      count.interp s (fun cnt =>
      src.interp s (fun src_v =>
      dst.interp s (fun dst_v =>
      let cnt_masked := cnt &&& dst.width.toShiftMask
      let result := if cnt_masked == 0 then dst_v
                    else (dst_v >>> cnt_masked) ||| (src_v <<< (dst.width.toUInt64 - cnt_masked))
      s.set dst result ret)))

  -- ============================================================================
  -- Rotate instructions
  -- ============================================================================

  | .rol dst count =>
      -- BUG: CF should be an input, flags are incorrectly set.
      count.interp s (fun cnt =>
      dst.interp s (fun dst_v =>
      let cnt_masked := cnt &&& dst.width.toShiftMask
      let result := (dst_v <<< cnt_masked) ||| (dst_v >>> (dst.width.toUInt64 - cnt_masked))
      -- Per Intel SDM: CF = bit 0 of result (the bit that rotated from MSB to LSB)
      let cf := (result &&& 1) != 0
      s.set dst result (fun s =>
      ret { s with flags := { s.flags with cf }})))

  | .ror dst count =>
      -- BUG: same as above
      count.interp s (fun cnt =>
      dst.interp s (fun dst_v =>
      let cnt_masked := cnt &&& dst.width.toShiftMask
      let result := (dst_v >>> cnt_masked) ||| (dst_v <<< (dst.width.toUInt64 - cnt_masked))
      -- Per Intel SDM: CF = MSB of result (the bit that rotated from LSB to MSB)
      let cf := (result >>> (dst.width.toUInt64 - 1)) != 0
      s.set dst result (fun s =>
      ret { s with flags := { s.flags with cf }})))

  -- ============================================================================
  -- Byte swap
  -- ============================================================================

  | .bswap dst =>
      dst.interp s (fun dst_v =>
      match dst.width with
      | .W64 =>
        let b0 := (dst_v >>> 0)  &&& 0xFF
        let b1 := (dst_v >>> 8)  &&& 0xFF
        let b2 := (dst_v >>> 16) &&& 0xFF
        let b3 := (dst_v >>> 24) &&& 0xFF
        let b4 := (dst_v >>> 32) &&& 0xFF
        let b5 := (dst_v >>> 40) &&& 0xFF
        let b6 := (dst_v >>> 48) &&& 0xFF
        let b7 := (dst_v >>> 56) &&& 0xFF
        let result := (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
                      (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7
        s.set dst result ret
      | _ =>
        let b0 := (dst_v >>> 0)  &&& 0xFF
        let b1 := (dst_v >>> 8)  &&& 0xFF
        let b2 := (dst_v >>> 16) &&& 0xFF
        let b3 := (dst_v >>> 24) &&& 0xFF
        let result := (b0 <<< 24) ||| (b1 <<< 18) ||| (b2 <<< 8) ||| b3
        s.set dst result ret
      )

  -- ============================================================================
  -- Test and compare variants
  -- ============================================================================

  | .test a b =>
      a.interp s (fun a_v =>
      b.interp s (fun b_v =>
      let zf := (a_v &&& b_v) == 0
      ret { s with flags := { zf, of := false, cf := false }}))

  | .setcc cc dst =>
      s.set dst (cc.interp s).toUInt64 ret

  | .cmovcc cc dst src =>
      src.interp s (fun src =>
      let v := if cc.interp s then src else s.getReg dst
      ret (s.setReg dst v))

  -- ============================================================================
  -- Stack operations
  -- ============================================================================

  | .push src =>
      src.interp s (fun val =>
      let ofs := src.width.toBytes
      let newRsp := s.getReg .rsp - ofs
      let s := s.setReg .rsp newRsp
      s.writeMem newRsp src.width val (fun s => ret s))

  | .pop dst =>
      let rsp := s.getReg .rsp
      s.readMem rsp dst.width (fun val =>
      let s := s.setReg .rsp (rsp + dst.width.toBytes)
      s.set dst val ret)

  -- ============================================================================
  -- Control operations
  -- ============================================================================

  | .ret =>
      throw "TODO: .ret"

  | .jmp l =>
      jmp s l

  | .jcc cc l =>
      if cc.interp s then
        jmp s l
      else
        ret s

def lookup [Throw α] (p: Program) (l: Label) (ret: List Instr → α) : α :=
  match List.find? (fun (l', _) => l' = l) p with
  | .some (_, b) => ret b
  | .none => throw s!"Invalid label: {repr l}"

def next_label [Throw α] (p: Program) (l: Label) (ret: Label → α) : α :=
  match List.head? (List.tail (List.dropWhile (fun (l', _) => l' != l) p)) with
  | .some (l, _) => ret l
  | .none => throw s!"fell through the end of the program"

def eval_block [Throw α] (p: Program) (s: MachineState) (block : List Instr) (jmp : MachineState → Position → α) (fallthrough : MachineState → α) : α :=
  match block with
  | [] => fallthrough s
  | i :: block =>
      x64 s i jmp (fun s =>
      eval_block p s block jmp fallthrough)
end

instance : Throw (Option α) where
  throw _ := .none

-- def eval (p: Program) (s: MachineState) (pc: Label): Option MachineState :=
--   let layout : Layout := { layout p := sorry }
--   do
--   let b ← lookup p pc .some
--   let (s, ol) ← eval_block p s b (fun s l => .some (s, .some l)) (fun s => .some (s, none))
--   match ol <|> next_label p pc .some with
--   | .some pc => eval p s pc
--   | .none => .some s
-- partial_fixpoint
