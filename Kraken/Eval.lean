import Lean
open Lean

syntax (name := eval_expr) "eval% " term : term
@[term_elab eval_expr]
unsafe def elabEvalExpr : Elab.Term.TermElab :=
  fun stx expectedType? => do
  let e ← Elab.Term.elabTerm stx[1] expectedType?
  let e ← instantiateMVars e
  let toExprCall ← Meta.mkAppM ``Lean.toExpr #[e]
  let e_reduced ← Meta.evalExpr Expr (.const ``Lean.Expr []) toExprCall
  return e_reduced

class ToTypeFamilyExpr {α : Type u} (β : α → Type v) where
  toTypeFamilyExpr : Expr

instance {α : Type u} {β : α → Type v}
  [ToLevel.{u}] [ToLevel.{v}]
  [ToExpr α] [∀ i, ToExpr (β i)] [ToTypeFamilyExpr β]
  : ToExpr (Sigma β) :=
  let eσ := mkConst ``Sigma [toLevel.{u}, toLevel.{v}]
  let eσmk := mkConst ``Sigma.mk [toLevel.{u}, toLevel.{v}]
  let eα := toTypeExpr α
  let eβ := ToTypeFamilyExpr.toTypeFamilyExpr β
  { toTypeExpr := mkApp2 eσ eα eβ
    toExpr s := mkApp4 eσmk eα eβ (toExpr s.1) (toExpr s.2) }

instance {α : Type u} {β : Type v} [ToLevel.{u}] [ToLevel.{v}] [ToExpr α] [ToExpr β]
  : ToTypeFamilyExpr (fun _ : α => β) :=
  { toTypeFamilyExpr := .lam `_x (toTypeExpr α) (toTypeExpr β) .default }

section _test
instance : ToTypeFamilyExpr (fun n : Nat => BitVec n) :=
  { toTypeFamilyExpr := .lam `n (.const ``Nat []) (.app (.const ``BitVec []) (.bvar 0)) .default }
inductive Foo | foo (_ : (n : Nat) × BitVec n ) deriving Lean.ToExpr
def p := eval% Foo.foo ⟨ 1, .ofBool true ⟩
/--
info: def p : Foo :=
Foo.foo ⟨1, 1#1⟩
-/
#guard_msgs in
#print p
end _test
