/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import Lean.Linter.Basic
import Std
import InfoGeometry.Meta.Trust
import InfoGeometry.Meta.Admission
import InfoGeometry.Meta.ArchitectureAudit
import InfoGeometry.Lint.WitnessLint
import InfoGeometry.Lint.NonTriviality

open Lean Elab Command InfoGeometry.Meta

namespace InfoGeometry.Lint

/-- Option to control the Pauli sorry linter. -/
register_option linter.pauli.admitUsage : Bool := {
  defValue := true
  descr := "report declarations in Canonical namespace depending on explicit sorryAx as visible closure debt"
}

register_option linter.pauli.admitUsageAsClosureDebt : Bool := {
  defValue := true
  descr := "treat explicit sorryAx as permitted closure debt instead of a hard warning; disguised substitutes remain lint targets"
}

/-- Option to control the Pauli grand unity linter. -/
register_option linter.pauli.grandUnity : Bool := {
  defValue := true
  descr := "warn about grand unity via trivial reflexivity"
}

/-- Option to control the Pauli witness-pack linter. -/
register_option linter.pauli.witness : Bool := {
  defValue := true
  descr := "warn about structures with generic Prop _statement/_sorry field pairs"
}

private def isCanonical (declName : Name) : Bool :=
  (`InfoGeometry.Canonical).isPrefixOf declName && declName != `InfoGeometry.Canonical

/-- True for any namespace under `InfoGeometry.`. -/
private def isInfoGeometry (declName : Name) : Bool :=
  (`InfoGeometry).isPrefixOf declName && declName != `InfoGeometry

/-- Resolve a possibly `_root_.`-qualified command identifier against `currNs`. -/
private def resolveScopedDeclName (currNs idName : Name) : Name :=
  if (`_root_).isPrefixOf idName then
    idName.replacePrefix `_root_ .anonymous
  else
    currNs ++ idName

/-- Extract the declaration identifier syntax across `structure`, `class`, `theorem`,
`def`, `abbrev`, `opaque`, `axiom`, and named `instance` commands. -/
private def extractDeclIdent? (decl : Syntax) : Option Syntax := Id.run do
  let mut stack := #[decl]
  while !stack.isEmpty do
    let current := stack.back!
    stack := stack.pop
    if current.getKind == ``Lean.Parser.Command.declId then
      let id := current[0]
      if id.isIdent then
        return some id
    else
      for child in current.getArgs do
        stack := stack.push child
  return none

/-- Strip leading lambda and metadata binders before checking direct `Eq.refl`/`rfl`. -/
private partial def stripLeadingLambdasAndMData : Expr → Expr
  | .lam _ _ body _ => stripLeadingLambdasAndMData body
  | .mdata _ body => stripLeadingLambdasAndMData body
  | e => e

/-- Detect equality propositions whose two sides are equal at `@[reducible]`
transparency (catching `Eq.symm rfl`, `congrArg id rfl`, or `Nat.add_comm n n` on
`X = X` without unfolding semireducible definitions or false-flagging computed identities). -/
private def hasReduciblyReflexiveEqualityType (type : Expr) : MetaM Bool := do
  Lean.Meta.forallTelescope type fun _ body =>
    Lean.Meta.withReducible do
      let body ← Lean.Meta.whnf body
      match body with
      | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
          Lean.Meta.isDefEq lhs rhs
      | _ =>
          pure false

/-- Total short leaf name extractor for declaration names. -/
private def declShortString : Name → String
  | .str _ s => s
  | n => toString n

private def isLemmaSyntaxKind (k : SyntaxNodeKind) : Bool :=
  k == `lemma || k == `Mathlib.Tactic.lemma || (toString k).endsWith ".lemma"

private def isDeclarationLikeCommand (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Lean.Parser.Command.declaration ||
    k == ``Lean.Parser.Command.mutual ||
    isLemmaSyntaxKind k

private partial def collectSyntaxDeclsAux
    (currNs : Name) (stx : Syntax) (acc : Array (Name × Syntax)) : Array (Name × Syntax) :=
  let k := stx.getKind
  if k == ``Lean.Parser.Command.in && stx[0].getKind == ``Lean.Parser.Command.set_option then
    collectSyntaxDeclsAux currNs stx[2] acc
  else if k == ``Lean.Parser.Command.declaration then
    match extractDeclIdent? stx[1] with
    | some id => acc.push (resolveScopedDeclName currNs id.getId, id)
    | none => acc
  else if isLemmaSyntaxKind k then
    match extractDeclIdent? stx with
    | some id => acc.push (resolveScopedDeclName currNs id.getId, id)
    | none => acc
  else if k == ``Lean.Parser.Command.mutual then
    stx[1].getArgs.foldl (init := acc) fun a child => collectSyntaxDeclsAux currNs child a
  else if stx.isOfKind `null then
    stx.getArgs.foldl (init := acc) fun a child => collectSyntaxDeclsAux currNs child a
  else
    acc

private partial def collectTreeDeclsAux
    (t : InfoTree) (fallbackStx : Syntax) (acc : Array (Name × Syntax)) : Array (Name × Syntax) :=
  match t with
  | .context (.parentDeclCtx parentDecl) child =>
      let acc' := acc.push (parentDecl, fallbackStx)
      collectTreeDeclsAux child fallbackStx acc'
  | .context _ child =>
      collectTreeDeclsAux child fallbackStx acc
  | .node info children =>
      let acc' :=
        match info with
        | .ofTermInfo ti =>
            if ti.isBinder && ti.expr.isConst then
              acc.push (ti.expr.constName!, ti.stx)
            else
              acc
        | _ => acc
      children.foldl (init := acc') fun a c => collectTreeDeclsAux c fallbackStx a
  | .hole _ => acc

private def isUserCommandDecl (queryEnv : Environment) (d : Name) : Bool :=
  (queryEnv.getModuleIdxFor? d).isNone &&
    (queryEnv.find? d).isSome &&
    !d.isInternal &&
    !d.isInternalDetail &&
    !Lean.isPrivateName d &&
    !d.hasMacroScopes &&
    !Lean.isAuxRecursor queryEnv d &&
    !Lean.isNoConfusion queryEnv d &&
    !Lean.isSparseCasesOn queryEnv d &&
    !(queryEnv.isConstructor d) &&
    !(queryEnv.isProjectionFn d)

/--
Linter for the Pauli Mandate.

This linter runs after each command and checks for violations of the
Axiom-Surface Seal, the Identity-via-Reflexivity audit, and the
Witness-Pack prohibition.
-/
def pauliLinter : Linter where
  run := Lean.withSetOptionIn fun stx => do
    let anyEnabled :=
      linter.pauli.admitUsage.get (← getOptions) ||
      linter.pauli.grandUnity.get (← getOptions) ||
      linter.pauli.witness.get (← getOptions)
    unless anyEnabled do
      return
    unless isDeclarationLikeCommand stx do
      return

    let env ← getEnv
    let queryEnv := env.setExporting false
    let currNs ← getCurrNamespace

    let syntaxCandidates := collectSyntaxDeclsAux currNs stx #[]
    let trees ← getInfoTrees
    let treeCandidates :=
      trees.foldl (init := #[]) fun acc t => collectTreeDeclsAux t stx acc

    let mut seen : Std.HashSet Name := {}
    let mut targets : Array (Name × Syntax) := #[]
    for (declName, idStx) in syntaxCandidates ++ treeCandidates do
      if isUserCommandDecl queryEnv declName && !seen.contains declName then
        seen := seen.insert declName
        targets := targets.push (declName, idStx)

    let physicalKeywords :=
      #["Einstein", "Boltzmann", "Hamiltonian", "Entropy", "Physics", "Gravity", "Condensate"]
    let foundationalNamespaces :=
      #[ "InfoGeometry.Core"
       , "InfoGeometry.Algebra"
       , "InfoGeometry.Thermo"
       , "InfoGeometry.Geometry"
       , "InfoGeometry.OperatorAlgebra"
       , "InfoGeometry.Krein"
       , "InfoGeometry.Modular"
       , "InfoGeometry.Clifford"
       , "InfoGeometry.Quantum" ]

    for (declName, idStx) in targets do
      -- ── 4. Witness-Pack detection (structure/class declarations) ──
      if Lean.isStructure queryEnv declName && isInfoGeometry declName then
        if linter.pauli.witness.get (← getOptions) then
          let pairs := detectWitnessPackPairs queryEnv declName
          for diag in renderAllWitnessPackDiags declName pairs do
            logError diag

      if isCanonical declName then
        if let some info := queryEnv.find? declName then
          -- 1. Axiom-Surface Seal
          if isAuditableDecl info && linter.pauli.admitUsage.get (← getOptions) then
            let axioms ← Lean.collectAxioms declName
            if axioms.contains ``sorryAx then
              if linter.pauli.admitUsageAsClosureDebt.get (← getOptions) then
                logInfo m!"[Pauli/Closure Debt] {declName} explicitly depends on `sorryAx`; permitted as honest closure debt, not eligible for contraction/deletion."
              else
                logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on `sorryAx`."
            let forbidden := forbiddenAxiomsOf axioms
            if !forbidden.isEmpty then
              logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on non-foundational axioms: {String.intercalate ", " (forbidden.map toString)}."

          -- 2. Grand Unity (rfl)
          if linter.pauli.grandUnity.get (← getOptions) && !Lean.Meta.isInstanceCore queryEnv declName then
            if let .thmInfo thmInfo := info then
              let coreBody := stripLeadingLambdasAndMData thmInfo.value
              let isDirectRfl := coreBody.isAppOfArity ``Eq.refl 2 || coreBody.isAppOfArity ``rfl 2
              let isReducibleRfl ←
                if isDirectRfl then pure false
                else liftTermElabM <| hasReduciblyReflexiveEqualityType thmInfo.type
              if isDirectRfl || isReducibleRfl then
                logError m!"[Pauli/Identity-via-Reflexivity] {declName} is proved via trivial `rfl`."
              else
                let auditResult ←
                  liftCoreM
                    (Meta.MetaM.run'
                      (auditExprTrivialityDetailed AuditConfig.default queryEnv [declName]
                        (AuditConfig.maxLocalUnfoldDepth AuditConfig.default) thmInfo.value))
                let metric := AuditResult.toMetric auditResult
                if !MathfulnessMetric.isGenuine metric then
                  logError m!"[Pauli/Identity-via-Reflexivity] {declName} recursively evaluates to a trivial/tautological proof. Metric: {repr metric}"

          -- 3. No-Mask Mandate (Heuristic)
          if isAuditableDecl info || Lean.isStructure queryEnv declName then
            let shortName := declShortString declName.eraseMacroScopes
            if physicalKeywords.any (fun kw => shortName.contains kw) then
              let hasFoundation :=
                InfoGeometry.Meta.ArchitectureAudit.reachesNamespacePrefix queryEnv declName foundationalNamespaces
              if !hasFoundation then
                logWarningAt idStx m!"[Pauli/No-Mask Mandate] {declName} uses a physically-loaded name but does not transitively depend on foundational Core or Algebra transformations. Ensure this is not symbolic inflation."

initialize addLinter pauliLinter

end InfoGeometry.Lint
