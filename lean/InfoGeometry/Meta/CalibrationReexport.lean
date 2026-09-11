import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Lean Elab Command Meta Term

namespace InfoGeometry.Meta

structure CalibrationReexportData where
  levelParams : List Name
  typeExpr : Expr
  valueExpr : Expr

private def collectPendingMVars (exprs : Array Expr) : TermElabM (Array MVarId) := do
  let mut seen : Std.HashSet Name := {}
  let mut pending : Array MVarId := #[]
  for expr in exprs do
    for mvarId in (← getMVars expr) do
      if !seen.contains mvarId.name then
        seen := seen.insert mvarId.name
        pending := pending.push mvarId
  pure pending

private def finalizeLevelParams (typeExpr valueExpr : Expr) : TermElabM CalibrationReexportData := do
  let typeExpr ← Term.levelMVarToParam typeExpr
  let valueExpr ← Term.levelMVarToParam valueExpr
  let typeExpr ← instantiateMVars typeExpr
  let valueExpr ← instantiateMVars valueExpr
  let levelParams := (collectLevelParams (collectLevelParams {} typeExpr) valueExpr).params.toList
  pure { levelParams, typeExpr, valueExpr }

private def elabCalibrationReexportDecl
    (declName : Name)
    (rhsStx : Syntax) : CommandElabM CalibrationReexportData := do
  liftTermElabM do
    Term.withDeclName declName do
      withoutModifyingEnv do
        let valueExpr ← Term.elabTerm rhsStx none false
        let valueExpr ← instantiateMVars valueExpr
        let typeExpr ← instantiateMVars (← inferType valueExpr)
        try
          Term.synthesizeSyntheticMVarsNoPostponing
        catch _ =>
          let pending ← collectPendingMVars #[valueExpr, typeExpr]
          discard <| Term.logUnassignedUsingErrorInfos pending
          throwError "calibration re-export `{declName}` left unresolved synthetic obligations."
        let pending ← collectPendingMVars #[typeExpr, valueExpr]
        if !pending.isEmpty then
          discard <| Term.logUnassignedUsingErrorInfos pending
          throwError "calibration re-export `{declName}` elaborated to an expression with unresolved metavariables."
        unless ← isProp typeExpr do
          throwError "calibration re-export `{declName}` does not have a proposition type"
        finalizeLevelParams typeExpr valueExpr

private def commitCalibrationReexportTheorem
    (declName : Name)
    (data : CalibrationReexportData) : CommandElabM Unit := do
  if (← getEnv).contains declName then
    throwError "declaration `{declName}` has already been declared"
  liftCoreM <| addDecl <| .thmDecl
    { name := declName
      levelParams := data.levelParams
      type := data.typeExpr
      value := data.valueExpr
    }

/--
Thin canonical re-export command for wrapper theorems.

It infers the theorem type from the supplied term and commits a kernel-checked
theorem with the current namespace prefix.
-/
elab "#calibration_reexport " declId:ident " := " rhs:term : command => do
  let declName := (← getCurrNamespace) ++ declId.getId
  let data ← elabCalibrationReexportDecl declName rhs.raw
  commitCalibrationReexportTheorem declName data

/-- Reusable proof-body macro for thin wrapper theorems. -/
macro "reexport " t:term : tactic => `(tactic| exact $t)

end InfoGeometry.Meta
