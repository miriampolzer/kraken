/-
Kraken Parser - x86_64 AT&T Assembly Parser

Parses AT&T syntax assembly strings into Kraken's Program type.
Uses Lean's built-in Std.Internal.Parsec library.

Compatible with Lean 4.22.0+.
-/

import Kraken.Semantics
import Std.Internal.Parsec.String

namespace Kraken.Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

-- ============================================================================
-- Basic Parsing Utilities
-- ============================================================================

/-- Skip zero or more horizontal whitespace characters (space, tab). -/
def skipHWs : Parser Unit := do
  let _ ← many (pchar ' ' <|> pchar '\t')

/-- Skip a line comment starting with # or //. -/
def skipLineComment : Parser Unit := do
  let _ ← pchar '#' <|> (pstring "//" *> pure '/')
  let _ ← many (satisfy fun c => c != '\n')
  pure ()

/-- Skip horizontal whitespace and comments on the same line. -/
def skipHWsAndComments : Parser Unit := do
  skipHWs
  (skipLineComment *> pure ()) <|> pure ()

/-- Parse a single decimal digit. -/
def digit : Parser Char := satisfy fun c => c >= '0' && c <= '9'

/-- Parse a single hex digit. -/
def hexDigit : Parser Char := satisfy fun c =>
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

/-- Parse a signed integer (decimal or hex). -/
def parseInt : Parser Int := do
  skipHWs
  let neg ← (pchar '-' *> pure true) <|> pure false
  let val ← parseHexOrDec
  pure (if neg then -val else val)
where
  hexVal (c : Char) : Int :=
    if c >= '0' && c <= '9' then c.toNat - '0'.toNat
    else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
    else c.toNat - 'A'.toNat + 10
  parseHexOrDec : Parser Int := do
    let c ← peek!
    if c == '0' then do
      skip
      let c2 ← peek!
      if c2 == 'x' || c2 == 'X' then do
        skip
        let digits ← many1 hexDigit
        pure (digits.foldl (fun acc d => acc * 16 + hexVal d) 0)
      else do
        let rest ← many digit
        let allDigits := #['0'] ++ rest
        pure (allDigits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)
    else do
      let digits ← many1 digit
      pure (digits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)

/-- Parse a name (identifier or label). -/
def parseName : Parser String := do
  let first ← satisfy fun c => c.isAlpha || c == '_' || c == '.'
  let rest ← many (satisfy fun c => c.isAlphanum || c == '_' || c == '.')
  pure (String.mk (#[first] ++ rest).toList)

-- ============================================================================
-- Register Parsing
-- ============================================================================

/-- Parse a register name. Returns the Reg and whether it was a 32-bit alias. -/
def parseRegName : Parser (Reg × Bool) := do
  let name ← parseName
  match name.toLower with
  -- 64-bit registers
  | "rax" => pure (.rax, false) | "rbx" => pure (.rbx, false)
  | "rcx" => pure (.rcx, false) | "rdx" => pure (.rdx, false)
  | "rsi" => pure (.rsi, false) | "rdi" => pure (.rdi, false)
  | "rsp" => pure (.rsp, false) | "rbp" => pure (.rbp, false)
  | "r8"  => pure (.r8,  false) | "r9"  => pure (.r9,  false)
  | "r10" => pure (.r10, false) | "r11" => pure (.r11, false)
  | "r12" => pure (.r12, false) | "r13" => pure (.r13, false)
  | "r14" => pure (.r14, false) | "r15" => pure (.r15, false)
  -- 32-bit aliases (zero-extend to 64-bit when written)
  | "eax" => pure (.rax, true) | "ebx" => pure (.rbx, true)
  | "ecx" => pure (.rcx, true) | "edx" => pure (.rdx, true)
  | "esi" => pure (.rsi, true) | "edi" => pure (.rdi, true)
  | "esp" => pure (.rsp, true) | "ebp" => pure (.rbp, true)
  | "r8d"  => pure (.r8,  true) | "r9d"  => pure (.r9,  true)
  | "r10d" => pure (.r10, true) | "r11d" => pure (.r11, true)
  | "r12d" => pure (.r12, true) | "r13d" => pure (.r13, true)
  | "r14d" => pure (.r14, true) | "r15d" => pure (.r15, true)
  | _ => fail s!"unknown register: {name}"

/-- Parse a register operand: %rax, %r15, etc. Returns (Reg, is32bit). -/
def parseReg : Parser (Reg × Bool) := do
  skipHWs
  let _ ← pchar '%'
  parseRegName

/-- Parse a register, requiring 64-bit. -/
def parseReg64 : Parser Reg := do
  let (r, is32) ← parseReg
  if is32 then fail "expected 64-bit register"
  else pure r

-- ============================================================================
-- Operand Parsing
-- ============================================================================

/-- Parse an immediate operand: $42, $-17, $0xff. -/
def parseImm : Parser Operand := do
  skipHWs
  let _ ← pchar '$'
  let v ← parseInt
  -- Validate range for Int64
  if v < -9223372036854775808 || v > 9223372036854775807 then
    fail s!"immediate {v} out of Int64 range"
  pure (.imm (Int64.ofInt v))

/-- Parse a memory operand: disp(%base), (%base,%idx,scale), etc. -/
def parseMemory : Parser Operand := do
  skipHWs
  -- Optional displacement
  let disp ← parseInt <|> pure 0
  let _ ← pchar '('
  skipHWs
  let base ← parseReg64
  -- Check for index register
  let idx ← (do
    skipHWs
    let _ ← pchar ','
    skipHWs
    let r ← parseReg64
    pure (some r)) <|> pure none
  -- Check for scale
  let scale ← match idx with
    | some _ => (do
        skipHWs
        let _ ← pchar ','
        skipHWs
        let s ← parseInt
        if s != 1 && s != 2 && s != 4 && s != 8 then
          fail s!"invalid scale {s}, must be 1, 2, 4, or 8"
        pure s.toNat) <|> pure 1
    | none => pure 1
  skipHWs
  let _ ← pchar ')'
  pure (.mem base idx scale disp)

/-- Parse any operand: register, immediate, or memory. -/
def parseOperand : Parser Operand := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let (r, _) ← parseReg
    pure (.reg r)
  else if c == '$' then
    parseImm
  else if c == '(' || c == '-' || c.isDigit then
    parseMemory
  else
    fail s!"expected operand, got '{c}'"

/-- Parse a register or memory operand (not immediate). -/
def parseRegOrMem : Parser Operand := do
  skipHWs
  let c ← peek!
  if c == '%' then
    let (r, _) ← parseReg
    pure (.reg r)
  else if c == '(' || c == '-' || c.isDigit then
    parseMemory
  else
    fail "expected register or memory operand"

-- ============================================================================
-- Condition Code Parsing
-- ============================================================================

/-- Parse a condition code from a conditional jump mnemonic suffix. -/
def parseCondCode (suffix : String) : Except String CondCode :=
  match suffix.toLower with
  | "z" | "e" => .ok .z
  | "nz" | "ne" => .ok .nz
  | "b" | "c" | "nae" => .ok .b
  | "ae" | "nc" | "nb" => .ok .ae
  | "a" | "nbe" => .ok .a
  | "be" | "na" => .ok .be
  | _ => .error s!"unknown condition code: {suffix}"

-- ============================================================================
-- Instruction Parsing
-- ============================================================================

/-- Parse a comma separator. -/
def parseComma : Parser Unit := do
  skipHWs
  let _ ← pchar ','
  skipHWs

/-- Parse an instruction mnemonic and its operands.
    AT&T syntax: src, dst (reversed from Intel). -/
def parseInstr : Parser Instr := do
  skipHWs
  let mnemonic ← parseName
  let mn := mnemonic.toLower
  -- Strip size suffix for matching
  let base :=
    if mn.endsWith "q" then mn.dropRight 1
    else if mn.endsWith "l" then mn.dropRight 1
    else mn
  match base with
  -- Arithmetic (two-operand: src, dst)
  | "add" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.add dst src)
  | "adc" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.adc dst src)
  | "adcx" => do
    let src ← parseRegOrMem; parseComma; let dst ← parseRegOrMem
    pure (.adcx dst src)
  | "adox" => do
    let src ← parseRegOrMem; parseComma; let dst ← parseRegOrMem
    pure (.adox dst src)
  | "sub" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.sub dst src)
  | "sbb" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.sbb dst src)
  | "mul" => do
    let src ← parseRegOrMem
    pure (.mul src)
  | "mulx" => do
    -- mulxq src, lo, hi (AT&T: src → rdx*src, result in lo:hi)
    let src ← parseRegOrMem; parseComma
    let lo ← parseRegOrMem; parseComma
    let hi ← parseRegOrMem
    pure (.mulx hi lo src)
  | "imul" => do
    let src ← parseRegOrMem; parseComma; let dst ← parseRegOrMem
    pure (.imul dst src)
  | "neg" => do
    let dst ← parseRegOrMem
    pure (.neg dst)
  | "dec" => do
    let dst ← parseRegOrMem
    pure (.dec dst)

  -- Move/Load
  | "mov" | "movabs" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    -- Check if this should be movl (32-bit suffix)
    if mn.endsWith "l" then
      pure (.movl dst src)
    else
      pure (.mov dst src)
  | "lea" => do
    let src ← parseMemory; parseComma
    let dst ← parseReg64
    pure (.lea dst src)

  -- Bitwise
  | "xor" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.xor dst src)
  | "and" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.and dst src)
  | "or" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.or dst src)

  -- Compare
  | "cmp" => do
    let src ← parseOperand; parseComma; let dst ← parseRegOrMem
    pure (.cmp dst src)

  -- Control flow - unconditional jump
  | "jmp" => do
    skipHWs
    let target ← parseName
    pure (.jmp target)

  -- Control flow - conditional jumps
  | _ =>
    if base.startsWith "j" then do
      match parseCondCode (base.drop 1) with
      | .ok cc => do
        skipHWs
        let target ← parseName
        pure (.jcc cc target)
      | .error msg => fail msg
    else
      fail s!"unsupported instruction: {mnemonic}"

-- ============================================================================
-- Label Parsing
-- ============================================================================

/-- Parse an optional label (name followed by colon).
    Uses attempt for proper backtracking if colon is not found. -/
def parseLabel : Parser (Option Label) := do
  skipHWs
  (attempt do
    let name ← parseName
    skipHWs
    let _ ← pchar ':'
    pure (some name)) <|> pure none

-- ============================================================================
-- Line and Program Parsing
-- ============================================================================

/-- Parse a single line: optional label, optional instruction.
    Returns None if the line is empty or comment-only. -/
def parseLine : Parser (Option (Option Label × Instr)) := do
  skipHWs
  let c ← peek!
  -- Skip empty lines and comment-only lines
  if c == '\n' || c == '#' then
    if c == '#' then skipLineComment
    pure none
  else
    -- Try to parse label
    let lbl ← parseLabel
    skipHWs
    let c2 ← peek!
    -- Check if there's an instruction after the label
    if c2 == '\n' || c2 == '#' then
      -- Label-only line (forward declaration) - not common, but handle it
      match lbl with
      | some l => fail s!"label '{l}' without instruction not supported"
      | none => pure none
    else
      let instr ← parseInstr
      pure (some (lbl, instr))

/-- Skip to the end of the current line. -/
def skipToEndOfLine : Parser Unit := do
  let _ ← many (satisfy fun c => c != '\n')
  let _ ← (pchar '\n' *> pure ()) <|> pure ()

/-- Parse multiple lines into a Program. -/
partial def parseProgramAux (acc : Program) : Parser Program := do
  skipHWs
  let done ← (eof *> pure true) <|> pure false
  if done then
    pure acc
  else
    let line ← parseLine
    skipToEndOfLine
    match line with
    | some entry => parseProgramAux (acc ++ [entry])
    | none => parseProgramAux acc

def parseProgram : Parser Program := parseProgramAux []

-- ============================================================================
-- Public API
-- ============================================================================

/-- Parse an assembly string into a Program.
    Returns an error message on failure. -/
def parse (input : String) : Except String Program :=
  match parseProgram input.mkIterator with
  | .success _ prog => .ok prog
  | .error _ msg => .error msg

/-- Parse an assembly string, panicking on failure (for use in #eval). -/
def parse! (input : String) : Program :=
  match parse input with
  | .ok prog => prog
  | .error msg => panic! s!"parse error: {msg}"

end Kraken.Parser

-- ============================================================================
-- Tests
-- ============================================================================

section Tests
open Kraken.Parser

-- Test: Simple instruction
#eval parse! "addq %rax, %rbx"
-- Expected: [(.none, .add (.reg .rbx) (.reg .rax))]

-- Test: Immediate operand
#eval parse! "movq $42, %rax"
-- Expected: [(.none, .mov (.reg .rax) (.imm 42))]

-- Test: Memory operand with displacement
#eval parse! "movq 8(%rsp), %rax"
-- Expected: [(.none, .mov (.reg .rax) (.mem .rsp .none 1 8))]

-- Test: Memory operand with index and scale
#eval parse! "movq (%rsi, %r15, 8), %rax"
-- Expected: [(.none, .mov (.reg .rax) (.mem .rsi (some .r15) 8 0))]

-- Test: Labeled instruction
#eval parse! "loop: addq $1, %rcx"
-- Expected: [(some "loop", .add (.reg .rcx) (.imm 1))]

-- Test: Conditional jump
#eval parse! "jnz loop"
-- Expected: [(.none, .jcc .nz "loop")]

-- Test: Multi-line program
#eval parse! "
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
"

-- Test: Negative immediate
#eval parse! "addq $-1, %rax"

-- Test: Hex immediate
#eval parse! "movq $0xff, %rax"

-- Test: mulx instruction
#eval parse! "mulxq %r8, %r9, %r10"

-- Test: xor for zeroing
#eval parse! "xorq %rax, %rax"

-- Test: lea with complex addressing
#eval parse! "leaq 16(%rbp, %rcx, 4), %rax"

end Tests
