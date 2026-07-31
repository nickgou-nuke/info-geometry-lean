import Lean
import InfoGeometry.Meta.Trust
import InfoGeometry.Meta.Admission
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
  (toString declName).startsWith "InfoGeometry.Canonical."

/-- True for any namespace under `InfoGeometry.`. -/
private def isInfoGeometry (declName : Name) : Bool :=
  (toString declName).startsWith "InfoGeometry."

/--
Linter for the Pauli Mandate.

This linter runs after each command and checks for violations of the
Axiom-Surface Seal, the Identity-via-Reflexivity audit, and the
Witness-Pack prohibition.
-/
def pauliLinter : Linter where
  run stx := do
    let anyEnabled :=
      linter.pauli.admitUsage.get (← getOptions) ||
      linter.pauli.grandUnity.get (← getOptions) ||
      linter.pauli.witness.get (← getOptions)
    unless anyEnabled do
      return

    let env ← getEnv
    -- We look for newly added declarations in the current command
    -- This is a bit tricky as a command can add multiple declarations.
    -- For now, we heuristically look at the syntax.

    let k := stx.getKind
    if k == ``Lean.Parser.Command.declaration then
      let decl := stx[1]
      let declKind := decl.getKind

      -- ── 4. Witness-Pack detection (structure declarations) ──
      -- This fires on `structure` commands, which are a separate
      -- declaration kind from theorem/definition/instance.
      if declKind == ``Lean.Parser.Command.structure ||
         declKind == ``Lean.Parser.Command.structureTk then
        if linter.pauli.witness.get (← getOptions) then
          -- Extract the structure name from the syntax
          let id := decl[1][0]
          if id.isIdent then
            let structName := (← getCurrNamespace) ++ id.getId
            if isInfoGeometry structName then
              let pairs := detectWitnessPackPairs env structName
              for diag in renderAllWitnessPackDiags structName pairs do
                logError diag

      if declKind == ``Lean.Parser.Command.theorem ||
         declKind == ``Lean.Parser.Command.definition ||
         declKind == ``Lean.Parser.Command.instance then
        let id := decl[1][0]
        if id.isIdent then
          let idName := id.getId
          let declName := (← getCurrNamespace) ++ idName
          if isCanonical declName then
            if let some info := env.find? declName then
              -- 1. Axiom-Surface Seal
              if linter.pauli.admitUsage.get (← getOptions) then
                let axioms ← Lean.collectAxioms declName
                if axioms.contains ``sorryAx then
                  if linter.pauli.admitUsageAsClosureDebt.get (← getOptions) then
                    logInfo m!"[Pauli/Closure Debt] {declName} explicitly depends on `sorryAx`; permitted as honest closure debt, not eligible for contraction/deletion."
                  else
                    logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on `sorryAx`."
                else if axioms.contains "admitAx".toName then
                  logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on nonstandard `admitAx`; use explicit `sorry` instead of a disguised placeholder."

              -- 2. Grand Unity (rfl)
              if linter.pauli.grandUnity.get (← getOptions) then
                if let some (.thmInfo info) := env.find? declName then
                  if info.value.isAppOfArity ``Eq.refl 2 || info.value.isAppOfArity ``rfl 2 then
                     logError m!"[Pauli/Identity-via-Reflexivity] {declName} is proved via trivial `rfl`."
                  else
                       let auditResult ←
                         liftCoreM
                           (Meta.MetaM.run'
                             (auditExprTrivialityDetailed AuditConfig.default env [declName]
                               (AuditConfig.maxLocalUnfoldDepth AuditConfig.default) info.value))
                       let metric := AuditResult.toMetric auditResult
                       if !MathfulnessMetric.isGenuine metric then
                         logError m!"[Pauli/Identity-via-Reflexivity] {declName} recursively evaluates to a trivial/tautological proof. Metric: {repr metric}"

            -- 3. No-Mask Mandate (Heuristic)
            let physicalKeywords := #["Einstein", "Boltzmann", "Hamiltonian", "Entropy", "Physics", "Gravity", "Condensate"]
            let nameStr := toString idName
            if physicalKeywords.any (fun k => nameStr.contains k) then
              let used := transitivelyUsedConstants env declName
              let mut hasFoundation := false
              for n in used do
                let s := toString n
                if s.startsWith "InfoGeometry.Core" || s.startsWith "InfoGeometry.Algebra" then
                  hasFoundation := true
                  break

              if !hasFoundation then
                logWarningAt id m!"[Pauli/No-Mask Mandate] {declName} uses a physically-loaded name but does not transitively depend on foundational Core or Algebra transformations. Ensure this is not symbolic inflation."
    else
      -- fallback for other kinds if they appear top-level
      pure ()

initialize addLinter pauliLinter

end InfoGeometry.Lint
