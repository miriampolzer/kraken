import Std
def BitVec.firstn (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
def BitVec.skipn (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' 0 (w-n)
def BitVec.replaceLow (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.skipn w) new).setWidth _
def BitVec.TODO_extend_signedness (x : BitVec w) {n : Nat} : BitVec n := x.setWidth _


instance : Coe UInt64 Nat where coe := UInt64.toNat
instance : Coe UInt32 Nat where coe := UInt32.toNat
instance : Coe UInt16 Nat where coe := UInt16.toNat
instance : Coe UInt8  Nat where coe := UInt8.toNat
instance : Coe UInt32 UInt64 where coe := UInt32.toUInt64
instance : Coe UInt16 UInt64 where coe := UInt16.toUInt64
instance : Coe UInt8  UInt64 where coe := UInt8.toUInt64
instance : Coe UInt16 UInt32 where coe := UInt16.toUInt32
instance : Coe UInt8  UInt32 where coe := UInt8.toUInt32
instance : Coe UInt8  UInt16 where coe := UInt8.toUInt16
attribute [coe] UInt64.toNat
attribute [coe] UInt32.toNat
attribute [coe] UInt16.toNat
attribute [coe] UInt8.toNat
attribute [coe] UInt32.toUInt64
attribute [coe] UInt16.toUInt32
attribute [coe] UInt8.toUInt32
attribute [coe] UInt16.toUInt32
attribute [coe] UInt8.toUInt32
attribute [coe] UInt8.toUInt16

inductive Width | W8 | W16 | W32 | W64 deriving Repr, BEq, DecidableEq
namespace Width
def bits : Width → Nat | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
def bytes : Width → Nat | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8
def type (w : Width) : Type := BitVec w.bits
def shiftmask : Width → Nat | W64 => 0x1f | _ => 0x0f -- "masked to 5 bits (or 6 bits with a 64-bit operand)"
end Width

inductive Reg64
| rax | rbx | rcx | rdx
| rsi | rdi | rsp | rbp
| r8  | r9  | r10 | r11
| r12 | r13 | r14 | r15
deriving Repr, BEq, DecidableEq

inductive Reg : Width → Type
| low (_ : Reg64) (w : Width) : Reg w
| ah : Reg .W8 | bh : Reg .W8 | ch : Reg .W8| dh : Reg .W8
deriving Repr, BEq, DecidableEq

namespace Reg
def base {w} (r : Reg w) : Reg64 := match r with
| .low r _ => r
| .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

def offset {w} (r : Reg w) : Nat := match r with
| .low _ _ => 0
| .ah | .bh | .ch | .dh => 8

@[match_pattern] abbrev rax := low .rax .W64
@[match_pattern] abbrev rbx := low .rbx .W64
@[match_pattern] abbrev rcx := low .rcx .W64
@[match_pattern] abbrev rdx := low .rdx .W64
@[match_pattern] abbrev rsi := low .rsi .W64
@[match_pattern] abbrev rdi := low .rdi .W64
@[match_pattern] abbrev rsp := low .rsp .W64
@[match_pattern] abbrev rbp := low .rbp .W64
@[match_pattern] abbrev r8  := low .r8  .W64
@[match_pattern] abbrev r9  := low .r9  .W64
@[match_pattern] abbrev r10 := low .r10 .W64
@[match_pattern] abbrev r11 := low .r11 .W64
@[match_pattern] abbrev r12 := low .r12 .W64
@[match_pattern] abbrev r13 := low .r13 .W64
@[match_pattern] abbrev r14 := low .r14 .W64
@[match_pattern] abbrev r15 := low .r15 .W64

@[match_pattern] abbrev eax  := low .rax .W32
@[match_pattern] abbrev ebx  := low .rbx .W32
@[match_pattern] abbrev ecx  := low .rcx .W32
@[match_pattern] abbrev edx  := low .rdx .W32
@[match_pattern] abbrev esi  := low .rsi .W32
@[match_pattern] abbrev edi  := low .rdi .W32
@[match_pattern] abbrev esp  := low .rsp .W32
@[match_pattern] abbrev ebp  := low .rbp .W32
@[match_pattern] abbrev r8d  := low .r8  .W32
@[match_pattern] abbrev r9d  := low .r9  .W32
@[match_pattern] abbrev r10d := low .r10 .W32
@[match_pattern] abbrev r11d := low .r11 .W32
@[match_pattern] abbrev r12d := low .r12 .W32
@[match_pattern] abbrev r13d := low .r13 .W32
@[match_pattern] abbrev r14d := low .r14 .W32
@[match_pattern] abbrev r15d := low .r15 .W32

@[match_pattern] abbrev ax   := low .rax .W16
@[match_pattern] abbrev bx   := low .rbx .W16
@[match_pattern] abbrev cx   := low .rcx .W16
@[match_pattern] abbrev dx   := low .rdx .W16
@[match_pattern] abbrev si   := low .rsi .W16
@[match_pattern] abbrev di   := low .rdi .W16
@[match_pattern] abbrev sp   := low .rsp .W16
@[match_pattern] abbrev bp   := low .rbp .W16
@[match_pattern] abbrev r8w  := low .r8  .W16
@[match_pattern] abbrev r9w  := low .r9  .W16
@[match_pattern] abbrev r10w := low .r10 .W16
@[match_pattern] abbrev r11w := low .r11 .W16
@[match_pattern] abbrev r12w := low .r12 .W16
@[match_pattern] abbrev r13w := low .r13 .W16
@[match_pattern] abbrev r14w := low .r14 .W16
@[match_pattern] abbrev r15w := low .r15 .W16

@[match_pattern] abbrev al   := low .rax .W8
@[match_pattern] abbrev bl   := low .rbx .W8
@[match_pattern] abbrev cl   := low .rcx .W8
@[match_pattern] abbrev dl   := low .rdx .W8
@[match_pattern] abbrev sil  := low .rsi .W8
@[match_pattern] abbrev dil  := low .rdi .W8
@[match_pattern] abbrev spl  := low .rsp .W8
@[match_pattern] abbrev bpl  := low .rbp .W8
@[match_pattern] abbrev r8b  := low .r8  .W8
@[match_pattern] abbrev r9b  := low .r9  .W8
@[match_pattern] abbrev r10b := low .r10 .W8
@[match_pattern] abbrev r11b := low .r11 .W8
@[match_pattern] abbrev r12b := low .r12 .W8
@[match_pattern] abbrev r13b := low .r13 .W8
@[match_pattern] abbrev r14b := low .r14 .W8
@[match_pattern] abbrev r15b := low .r15 .W8

end Reg

structure Reg64s where
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
deriving Repr, BEq, DecidableEq

def Reg64s.get64 (s : Reg64s) (r : Reg64) : Width.W64.type := UInt64.toBitVec (match r with
| .rax => s.rax | .rbx => s.rbx | .rcx => s.rcx | .rdx => s.rdx
| .rsi => s.rsi | .rdi => s.rdi | .rsp => s.rsp | .rbp => s.rbp
| .r8  => s.r8  | .r9  => s.r9  | .r10 => s.r10 | .r11 => s.r11
| .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15)

def Reg64s.set64 (regs : Reg64s) (r : Reg64) (v : Width.W64.type) (v := UInt64.ofBitVec v) : Reg64s := match r with
| .rax => { regs with rax := v } | .rbx => { regs with rbx := v }
| .rcx => { regs with rcx := v } | .rdx => { regs with rdx := v }
| .rsi => { regs with rsi := v } | .rdi => { regs with rdi := v }
| .rsp => { regs with rsp := v } | .rbp => { regs with rbp := v }
| .r8  => { regs with r8  := v } | .r9  => { regs with r9  := v }
| .r10 => { regs with r10 := v } | .r11 => { regs with r11 := v }
| .r12 => { regs with r12 := v } | .r13 => { regs with r13 := v }
| .r14 => { regs with r14 := v } | .r15 => { regs with r15 := v }

def Reg64s.get (s : Reg64s) {w} (r : Reg w) : w.type :=
  ((s.get64 r.base).skipn r.offset).firstn w.bits
  -- BitVec because it may be signed or unsigned depending on context

def Reg64s.set (s : Reg64s) (r : Reg w) (v : w.type) : Reg64s := match r with
| .low r .W64 => s.set64 r v
| .low r .W32 => s.set64 r (v.zeroExtend _)
| .low r w => s.set64 r ((s.get64 r).replaceLow v)
| .ah | .bh | .ch | .dh => let old := s.get64 r.base;
  s.set64 r.base (old.replaceLow (BitVec.append v (s.get (.low r.base .W8))))

structure Flags where
  zf : Bool := false
  of : Bool := false
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
deriving Repr, BEq, DecidableEq

abbrev DataMem := Std.ExtHashMap UInt64 UInt64 -- 8-byte-aligned acceses only now
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  flags : Flags := {}
  dmem : DataMem := ∅
deriving Repr, BEq, DecidableEq

class Throw α where
  throw: String → α

def throw {α} [inst: Throw α] :=
  inst.throw

def MachineData.load [Throw α] (s : MachineData) (addr : BitVec 64) (w : Width) (ret : w.type → α): α :=
  let addr := UInt64.ofBitVec addr;
  if addr % 8 != 0 then
    throw (s!"Unimplemented: only 8-byte-aligned memory access is supported")
  else match s.dmem[addr]? with
  | .some v => ret (v.toBitVec.truncate _)
  | .none => throw (s!"Memory read but not written to (addr={repr addr})")

def MachineData.store [Throw α] (s : MachineData) (addr : BitVec 64) {w : Width} (v : w.type) (ret: MachineData → α) : α :=
  s.load addr .W64 (fun old =>
  ret { s with dmem := s.dmem.insert (UInt64.ofBitVec addr) (UInt64.ofBitVec (old.replaceLow v)) })

abbrev Label := String
abbrev Position := Label × Nat
def Position.Label (l : Label) : Position := (l, 0)
def Position.next : Position → Position | (p, i) => (p, i+1)
instance : Coe Label Position where coe := Position.Label
attribute [coe] Position.Label

class Layout where layout: Position → UInt64
def layout [inst: Layout] := inst.layout
def label [inst: Layout] l := inst.layout (l, 0)

inductive ConstExpr
| Label (_ : Label)
| UInt64 (_ : UInt64)
| before_current_instruction | after_current_instruction
| add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
-- Careful adding operations here! Need to match overflow behavior of all
-- assemblers we want compatibility with. We assume oversized literals error;
-- clang and gcc seem to always use 64-bit arithmetic (MCValue has an int64).
deriving Repr, BEq, DecidableEq
instance : Coe Label ConstExpr where coe := ConstExpr.Label
instance : Coe UInt64 ConstExpr where coe := ConstExpr.UInt64
attribute [coe] ConstExpr.Label
attribute [coe] ConstExpr.UInt64

def ConstExpr.interp [Layout] : ConstExpr → Position → _root_.UInt64
| .Label l, _ => label l
| .UInt64 i, _ => i
| .before_current_instruction, pc => layout pc
| .after_current_instruction, pc => layout pc.next
| .add e1 e2, p => e1.interp p + e2.interp p
| .sub e1 e2, p => e1.interp p - e2.interp p

inductive RegOrRip (w : Width) | Reg (_ : Reg w) | Rip
deriving Repr, BEq, DecidableEq

structure AddrExpr where
  base : Option (Σ w, RegOrRip w)
  idx : Option ((Σ w, Reg w) × Width)
  disp : ConstExpr := .UInt64 0
deriving Repr, BEq, DecidableEq

def RipRel {w : Width} (e : ConstExpr) : AddrExpr := .mk (.some ⟨w, .Rip⟩) .none (.sub e .after_current_instruction)

class AddressSize where address_size : Width
def address_size [inst: AddressSize] := inst.address_size

def AddrExpr.interp [Layout] [AddressSize] (a : AddrExpr) (s : Reg64s) (p : Position) : address_size.type :=
  let base := match a.base with | .some ⟨_, .Reg r⟩ => (s.get r).toNat | .some ⟨_, .Rip⟩ => layout p.next | .none => 0
  let idx := match a.idx with | .some (⟨_, r⟩, w) => (s.get r).toNat * w.bytes | .none => 0
  BitVec.ofNat address_size.bits (base + idx + a.disp.interp p)

inductive RegOrMem w | Reg (r : Reg w) | mem (_ : AddrExpr)
deriving Repr, BEq, DecidableEq
instance : Coe AddrExpr (RegOrMem w) where coe := RegOrMem.mem
attribute [coe] RegOrMem.mem
instance : Coe (Reg w) (RegOrMem w) where coe := RegOrMem.Reg
attribute [coe] RegOrMem.Reg
abbrev Dst := RegOrMem

def RegOrMem.interp [Layout] [AddressSize] [Throw α] (o : RegOrMem w) (s : MachineData) (p : Position) (ret : w.type → α) :=
  match o with
  | .Reg r => ret (s.regs.get r)
  | .mem a => s.load (a.interp s.regs p).TODO_extend_signedness w ret

def MachineData.set [Layout] [AddressSize] [Throw α] (s : MachineData) (o : Dst w) (v : w.type) (p : Position) (ret : MachineData → α) : α :=
  match o with
  | .Reg r => ret {s with regs := s.regs.set r v}
  | .mem o => s.store (o.interp s.regs p).TODO_extend_signedness v ret

inductive Operand w | RegOrMem (_ : RegOrMem w) | imm (v : ConstExpr)
deriving Repr, BEq, DecidableEq
instance : Coe (RegOrMem w) (Operand w) where coe := Operand.RegOrMem
attribute [coe] Operand.RegOrMem
instance : Coe ConstExpr (Operand w) where coe := Operand.imm
attribute [coe] Operand.imm
abbrev Operand.reg (r : Reg w) : Operand w := .RegOrMem (.Reg r)
abbrev Operand.mem (m : AddrExpr) : Operand w := .RegOrMem (.mem m)

def Operand.interp [Layout] [AddressSize] [Throw α] (o : Operand w) (s : MachineData) (p : Position) (ret : w.type → α) :=
  match o with
  | .RegOrMem rm => rm.interp s p ret
  | .imm v => ret ((v.interp p).toBitVec.truncate _)

inductive CondCode | z | nz | c | nc | a | be
deriving Repr, BEq, DecidableEq
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

def CondCode.interp (cc : CondCode) (s : Flags) : Bool := match cc with
| .z  => s.zf | .nz => !s.zf | .c  => s.cf | .nc => !s.cf
| .a  => !s.cf && !s.zf | .be => s.cf || s.zf

inductive Operation (w : Width)
-- Data movement
| mov   (_ : Dst w) (src : Operand w)
| movzx (_ : Dst w) (src : Operand w)
| push (src : Operand w)
| pop  (_ : Dst w)
| setcc (_ : CondCode) (_ : Dst w)
| cmovcc (_ : CondCode) (_ : Reg w) (src : RegOrMem w)
-- Arithmetic
| lea (_ : Reg w) (src : AddrExpr)
| add  (_ : Dst w) (src : Operand w)
| adc  (_ : Dst w) (src : Operand w)
| adcx (_ : Reg w) (src : Operand w)
| adox (dst : Reg w) (src : Operand w)
| sub  (_ : Dst w) (src : Operand w)
| sbb  (_ : Dst w) (src : Operand w)
| mul  (src : RegOrMem w)
| mulx (hi lo : Reg w) (src : RegOrMem w)
| imul (_ : Dst w) (src : Operand w)
| neg  (_ : Dst w)
| dec  (_ : Dst w)
| test (a b : Operand w)
| cmp  (a : RegOrMem w) (b : Operand w)
-- Bitwise
| xor  (_ : Dst w) (src : Operand w)
| and  (_ : Dst w) (src : Operand w)
| or   (_ : Dst w) (src : Operand w)
| shl  (_ : Dst w) (count : Operand w)
| shr  (_ : Dst w) (count : Operand w)
| sar  (_ : Dst w) (count : Operand w)
| shld (_ : Dst w) (src count : Operand w)
| shrd (_ : Dst w) (src count : Operand w)
| rol  (_ : Dst w) (count : Operand w)
| ror  (_ : Dst w) (count : Operand w)
| bswap  (dst : Reg w) (_ : w = .W32 ∨ w = .W64) 
-- Control flow
| jcc (cc : CondCode) (target : Label)
| call (target : AddrExpr)
| jmp (target : AddrExpr)
| ret
| nop (length : Nat)
| nopalign (alignment : Nat) (max_skip : Nat)
deriving Repr, BEq, DecidableEq

structure Instruction where
  address_size : Width
  operation_size : Width
  operation : Operation operation_size
deriving Repr, DecidableEq

inductive Block
| code (global : Bool) (_ : List Instruction)
| data (_ : List UInt8)

def Program := List (Label × Block)

/-
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

def Reg.interp (r : Reg) (s : MachineData) (ret : UInt64 → α) :=
  ret (s.getReg r)

-/
section
variable [Layout]

variable [Throw α]


-- The reference semantics are taken from https://www.felixcloutier.com/x86/,
-- which itself is just extracted from https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
def x64 [Layout] [AddressSize] [Throw α] (p : Position) (s : MachineData) (i : Operation w) (jmp : MachineData → Position → α) (ret : MachineData → α): α :=
  match i with
  | .mov dst src =>
      -- If we leave aside segment-related operations, MOV is homogenous (i.e.
      -- src and dst have the same width). The only case that performs
      -- sign-extension is when dst = 64-bit register, and src = 32-bit
      -- immediate, in which case Operand.interp takes care of sign-extending.
      src.interp s p (fun val =>
      s.set dst val p ret)

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
      let rax_v := s.getReg (Reg.low .rax w)
      let result := rax_v.toNat * src_v.toNat
      if w != .W8 then
        let lo := (UInt64.ofNat result) &&& w.toMask
        let hi := UInt64.ofNat (result >>> w.toNat)
        let r_lo := Reg.low .rax w
        let r_hi := Reg.low .rdx w
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
      let src2_v := s.getReg (Reg.low .rdx w)
      let result := src1_v.toNat * src2_v.toNat
      -- Semantics say that if hi and lo are aliased, the value written is hi
      let s := s.setReg (r_lo.low w) (UInt64.ofNat result)
      let s := s.setReg (r_hi.low w) (UInt64.ofNat (result >>> w.toNat))
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

  | .bswap dst => -- TODO SDM: :16-bit bswap result is undefined
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
      s.load rsp dst.width (fun val =>
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

def eval_block [Throw α] (p: Program) (s: MachineData) (block : List Instr) (jmp : MachineData → Position → α) (fallthrough : MachineData → α) : α :=
  match block with
  | [] => fallthrough s
  | i :: block =>
      x64 s i jmp (fun s =>
      eval_block p s block jmp fallthrough)
end

instance : Throw (Option α) where
  throw _ := .none

-- def eval (p: Program) (s: MachineData) (pc: Label): Option MachineData :=
--   let layout : Layout := { layout p := sorry }
--   do
--   let b ← lookup p pc .some
--   let (s, ol) ← eval_block p s b (fun s l => .some (s, .some l)) (fun s => .some (s, none))
--   match ol <|> next_label p pc .some with
--   | .some pc => eval p s pc
--   | .none => .some s
-- partial_fixpoint
