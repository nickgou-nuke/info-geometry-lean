import Lean

/-!
# InfoGeometry.Meta.BridgeTarget

Macro infrastructure for bridge-target closure contracts.

A **bridge target** is a theorem-level bridge surface that should be machine-
visible to architecture audits. The `#bridge_reexport` command creates a
kernel-checked theorem, tags it as a bridge target, and keeps the wrapper
surface thin.

This is intentionally parallel to `InfoGeometry.Meta.OwnerTarget`, but it is
for transport/preservation theorems rather than owner contracts.
-/

open Lean Elab Command Meta Term

namespace InfoGeometry.Meta

/-- Tag attribute marking a theorem as a bridge-target surface. -/
initialize bridgeTargetTagAttr : TagAttribute ←
  registerTagAttribute `bridge_target_tag
    "Mark a theorem as a bridge-target surface for architecture auditing."

/-- Decapitalize the first character of a string. -/
private def decapitalizeFirst (s : String) : String :=
  if s.isEmpty then s
  else
    let first := s.front
    let rest := s.drop 1
    s!"{first.toLower}{rest}"

/-- Audit all bridge targets in the current environment. -/
def checkBridgeTargets : CoreM Unit := do
  let env ← getEnv
  let mut total := 0
  let mut proved := 0
  let mut debt : Array Name := #[]
  for (declName, _) in env.constants do
    if bridgeTargetTagAttr.hasTag env declName then
      total := total + 1
      let axioms ← Lean.collectAxioms declName
      if axioms.contains ``sorryAx then
        debt := debt.push declName
      else
        proved := proved + 1
  if debt.isEmpty then
    logInfo m!"Bridge Target Audit PASS: {proved}/{total} bridge targets fully discharged."
  else
    for d in debt do
      logError m!"BRIDGE TARGET DEBT: {d}"
    logInfo m!"Bridge Target Audit: {proved}/{total} proved, {debt.size} with closure debt."

/-- Reusable proof-body macro for thin bridge theorems. -/
macro "bridge" t:term : tactic => `(tactic| exact $t)

private structure BridgeReexportData where
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

private def finalizeLevelParams (typeExpr valueExpr : Expr) :
    TermElabM BridgeReexportData := do
  let typeExpr ← Term.levelMVarToParam typeExpr
  let valueExpr ← Term.levelMVarToParam valueExpr
  let typeExpr ← instantiateMVars typeExpr
  let valueExpr ← instantiateMVars valueExpr
  let levelParams := (collectLevelParams (collectLevelParams {} typeExpr) valueExpr).params.toList
  pure { levelParams, typeExpr, valueExpr }

private def elabBridgeReexportDecl
    (declName : Name)
    (rhsStx : Syntax) : CommandElabM BridgeReexportData := do
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
          throwError "bridge re-export `{declName}` left unresolved synthetic obligations."
        let pending ← collectPendingMVars #[typeExpr, valueExpr]
        if !pending.isEmpty then
          discard <| Term.logUnassignedUsingErrorInfos pending
          throwError "bridge re-export `{declName}` elaborated to an expression with unresolved metavariables."
        unless ← isProp typeExpr do
          throwError "bridge re-export `{declName}` does not have a proposition type"
        finalizeLevelParams typeExpr valueExpr

private def commitBridgeReexportTheorem
    (declName : Name)
    (data : BridgeReexportData) : CommandElabM Unit := do
  if (← getEnv).contains declName then
    throwError "declaration `{declName}` has already been declared"
  liftCoreM <| addDecl <| .thmDecl
    { name := declName
      levelParams := data.levelParams
      type := data.typeExpr
      value := data.valueExpr
    }
  let attrStx ← `(attribute [bridge_target_tag] $(mkIdent declName))
  elabCommand attrStx

/--
Thin canonical re-export command for bridge theorems.

It infers the theorem type from the supplied term, commits a kernel-checked
theorem with the current namespace prefix, and tags it as a bridge target.
-/
elab "#bridge_reexport " declId:ident " := " rhs:term : command => do
  let declName := (← getCurrNamespace) ++ declId.getId
  let data ← elabBridgeReexportDecl declName rhs.raw
  commitBridgeReexportTheorem declName data

/-- Command entrypoint for the bridge-target audit. -/
elab "#audit_bridge_targets" : command => do
  Command.liftCoreM checkBridgeTargets

end InfoGeometry.Meta
