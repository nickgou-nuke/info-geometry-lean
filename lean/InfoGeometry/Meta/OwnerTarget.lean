import Lean

/-!
# InfoGeometry.Meta.OwnerTarget

Macro infrastructure for owner-target closure contracts.

An **owner target** is a module's self-declaration of what it must prove: a
`Prop`-valued conjunction of all identities owned by the module, together with
a kernel-checked proof discharging every clause.

## Usage

```lean
owner_target PrimeMajoranaPfaffian
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) where
  blockPfaffian P q = InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q
```

expands to:

```lean
@[owner_target_tag]
def PrimeMajoranaPfaffianOwnerTarget : Prop :=
  ∀ (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ),
    blockPfaffian P q = InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q

theorem primeMajoranaPfaffianOwnerTarget :
    PrimeMajoranaPfaffianOwnerTarget := by
  -- obligation: fill in the proof here
```

For multiple owned identities, list them separated by newlines after `where`.
They are combined into an `∧`-conjunction automatically.

## Design

- The `@[owner_target_tag]` attribute marks the `def` so that tooling
  (`#audit_owner_targets`, `sorry_analyzer.py`, graph overlay) can enumerate
  all owner-target surfaces programmatically.
- The theorem name is the `lowerCamelCase` version of the definition name.
- The macro does not fill the proof; the module author must discharge it.
  A `sorry` in an owner-target proof is machine-visible closure debt.

This directly encodes the Owner-Target pattern described in Black Book
Chapter 104 (2-Categorical Skeleton) as compiler-checked structure.
-/

open Lean Elab Command

namespace InfoGeometry.Meta

/-- Tag attribute marking `def`s that are owner-target closure contracts. -/
initialize ownerTargetTagAttr : TagAttribute ←
  registerTagAttribute `owner_target_tag
    "Mark a definition as an owner-target closure contract for architecture auditing."

/-- Decapitalize the first character of a string. -/
private def decapitalizeFirst (s : String) : String :=
  if s.isEmpty then s
  else
    let first := s.front
    let rest := s.drop 1
    s!"{first.toLower}{rest}"

/-- Audit all owner targets in the current environment. -/
def checkOwnerTargets : CoreM Unit := do
  let env ← getEnv
  let mut total := 0
  let mut proved := 0
  let mut debtDecls : Array Name := #[]
  for (declName, _) in env.constants do
    if ownerTargetTagAttr.hasTag env declName then
      total := total + 1
      -- Convention: FooOwnerTarget (def) → fooOwnerTarget (theorem)
      -- Extract last component, decapitalize first letter, reconstruct
      let components := declName.components
      match components.reverse with
      | last :: rest =>
        let lastStr := toString last
        let thmLastStr := decapitalizeFirst lastStr
        let ns := rest.reverse.foldl (init := Name.anonymous) fun acc n => Name.mkStr acc (toString n)
        let thmName := Name.mkStr ns thmLastStr
        if let some _ := env.find? thmName then
          let axioms ← Lean.collectAxioms thmName
          if axioms.contains ``sorryAx then
            debtDecls := debtDecls.push thmName
          else
            proved := proved + 1
        else
          debtDecls := debtDecls.push declName
      | [] =>
        debtDecls := debtDecls.push declName
  if debtDecls.isEmpty then
    logInfo m!"Owner Target Audit PASS: {proved}/{total} owner targets fully discharged."
  else
    for d in debtDecls do
      logError m!"OWNER TARGET DEBT: {d}"
    logInfo m!"Owner Target Audit: {proved}/{total} proved, {debtDecls.size} with closure debt."

/-- Command entrypoint for the owner-target audit. -/
elab "#audit_owner_targets" : command => do
  Command.liftCoreM checkOwnerTargets

end InfoGeometry.Meta
