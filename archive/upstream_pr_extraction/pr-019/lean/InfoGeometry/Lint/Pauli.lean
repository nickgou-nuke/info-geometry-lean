import Lean
import InfoGeometry.Meta.Trust
import InfoGeometry.Meta.Admission

open Lean Elab Command InfoGeometry.Meta

namespace InfoGeometry.Lint

/-- Option to control the Pauli sorry linter. -/
register_option linter.pauli.sorry : Bool := {
  defValue := true
  descr := "warn about declarations in Canonical namespace depending on sorryAx"
}

/-- Option to control the Pauli grand unity linter. -/
register_option linter.pauli.grandUnity : Bool := {
  defValue := true
  descr := "warn about grand unity via trivial reflexivity"
}

private def isCanonical (declName : Name) : Bool :=
  (toString declName).startsWith "InfoGeometry.Canonical."

/--
Linter for the Pauli Mandate.

This linter runs after each command and checks for violations of the
Axiom-Surface Seal and the Identity-via-Reflexivity audit.
-/
def pauliLinter : Linter where
  run stx := do
    unless linter.pauli.sorry.get (← getOptions) || linter.pauli.grandUnity.get (← getOptions) do
      return

    let env ← getEnv
    -- We look for newly added declarations in the current command
    -- This is a bit tricky as a command can add multiple declarations.
    -- For now, we heuristically look at the syntax.
    
    let k := stx.getKind
    if k == ``Lean.Parser.Command.declaration then
      let decl := stx[1]
      let declKind := decl.getKind
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
              if linter.pauli.sorry.get (← getOptions) then
                let axioms ← Lean.collectAxioms declName
                if axioms.contains ``sorryAx || axioms.contains "admitAx".toName then
                  logWarningAt id m!"[Pauli/Axiom-Surface Seal] {declName} depends on `sorryAx` or `admitAx`."
              
              -- 2. Grand Unity (rfl)
              if linter.pauli.grandUnity.get (← getOptions) then
                if let some (.thmInfo info) := env.find? declName then
                  if info.value.isAppOfArity ``Eq.refl 2 || info.value.isAppOfArity ``rfl 2 then
                     logWarningAt id m!"[Pauli/Identity-via-Reflexivity] {declName} is proved via trivial `rfl`. Ensure this is not masking missing logic."
            
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
