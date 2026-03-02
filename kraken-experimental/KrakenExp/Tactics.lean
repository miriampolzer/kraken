/-
Kraken - Proof Tactics (Experimental)

Advanced tactics for stepping through assembly proofs.
Requires Lean 4.28.0+ for SymM infrastructure.

For basic tactics, see Kraken/Tactics.lean.
For semantics, see Kraken/Semantics.lean.
-/

import Lean
import Lean.Meta.Sym.Grind
import Kraken.Tactics

open Lean Meta Sym Elab Tactic

-- Advanced tactic: use SymM to apply theorems with better automation
def sapply (lem : Name) (mvarId : MVarId) : SymM (List (MVarId)) := do
  let rule ← mkBackwardRuleFromDecl lem
  let .goals gs ← rule.apply mvarId | failure
  return gs

-- STEP TACTIC: version using SymM (more automated than apply step_cps)
syntax "step_cps_v2" : tactic
macro_rules
  | `(tactic|step_cps_v2) =>
  `(tactic|
    run_tac liftMetaTactic (λ g => SymM.run (sapply `step_cps g))
  )
