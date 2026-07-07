import Lean
import InfoGeometry.Lint.WitnessLint

open Lean Meta Elab Command

namespace InfoGeometry.Lint

/-- 
Recursively analyzes proof terms to ensure they depend on Mathlib axioms 
or non-trivial constant applications rather than purely identity reflexivities.
-/
partial def auditExprTriviality (e : Expr) : MetaM Bool := do
  match e.consumeMData with
  | Expr.app fn arg => 
      let fnGenuine ← auditExprTriviality fn
      let argGenuine ← auditExprTriviality arg
      return fnGenuine ∨ argGenuine
  | Expr.const declName _ =>
      if declName == ``Eq.refl ∨ declName == ``Iff.rfl then 
        return false 
      else 
        return true
  | Expr.sort _ => return false
  | _ => return true

/--
Integrates deep expression auditing with the existing command-level Pauli linter.
-/
def verifyDeclarationNonTriviality (env : Environment) (declName : Name) : MetaM (Option MessageData) := do
  match env.find? declName with
  | some (.thmInfo info) =>
      let isGenuine ← auditExprTriviality info.value
      if !isGenuine then
        return some m!"[Pauli/AST-Vacuity] `{declName}` consists entirely of trivial identities. Proof rejected."
      else
        return none
  | _ => return none

end InfoGeometry.Lint