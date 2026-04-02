import Lean
import Kraken.Eval
import Kraken.Semantics
deriving instance Lean.ToExpr for Width
deriving instance Lean.ToExpr for Reg64
deriving instance Lean.ToExpr for Reg
deriving instance Lean.ToExpr for ConstExpr
deriving instance Lean.ToExpr for RegOrRip
instance : ToTypeFamilyExpr (fun w : Width => Reg w) :=
  { toTypeFamilyExpr := .lam `w (.const ``Width []) (.app (.const ``Reg []) (.bvar 0)) .default }
deriving instance Lean.ToExpr for AddrIndex
instance : ToTypeFamilyExpr (fun w : Width => RegOrRip w) :=
  { toTypeFamilyExpr := .lam `w (.const ``Width []) (.app (.const ``RegOrRip []) (.bvar 0)) .default }
deriving instance Lean.ToExpr for AddrExpr
deriving instance Lean.ToExpr for RegOrMem
deriving instance Lean.ToExpr for Operand
deriving instance Lean.ToExpr for CondCode
deriving instance Lean.ToExpr for ShiftCountExpr
deriving instance Lean.ToExpr for RelRegOrMem
deriving instance Lean.ToExpr for Operation
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for ByteArray
deriving instance Lean.ToExpr for Directive
