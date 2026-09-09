import Lean
import InfoGeometry.Canonical.SpineAttributes

/-!
# scripts.DAG.Exploration.FunctorDiagnostics

Simple diagnostic for the `@[spine_functor]` taxonomy.

Usage:
`lake env lean --run lean/scripts/DAG/Exploration/FunctorDiagnostics.lean [module] [namespace]`

Defaults:
- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
-/

open Lean
open InfoGeometry.Canonical

private def defaultModule : String :=
  "InfoGeometry.Canonical.All"

private def defaultNamespace : String :=
  "InfoGeometry"

private def argD (args : Array String) (idx : Nat) (fallback : String) : String :=
  args.getD idx fallback

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => a.toString < b.toString

private def spineFunctorDecls (env : Environment) (ns? : Option Name := none) : Array Name :=
  sortNames <| env.constants.fold (init := #[]) fun acc declName _ =>
    if let some ns := ns? then
      if !ns.isPrefixOf declName then
        acc
      else if isSpineFunctor env declName then
        acc.push declName
      else
        acc
    else if isSpineFunctor env declName then
      acc.push declName
    else
      acc

private def printGroup (title : String) (decls : Array Name) : IO Unit := do
  IO.println title
  if decls.isEmpty then
    IO.println "  <none>"
  else
    for declName in decls do
      IO.println s!"  {declName}"

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)

  let argv := args.toArray
  let moduleStr := argD argv 0 defaultModule
  let namespaceStr := argD argv 1 defaultNamespace
  let moduleName := moduleStr.toName
  let namespaceName := namespaceStr.toName

  let env ← Lean.importModules #[{ module := moduleName }] {}
  let decls := spineFunctorDecls env (some namespaceName)
  let lifts := decls.filter (isSpineFunctorLift env ·)
  let constructors := decls.filter (isSpineFunctorConstructor env ·)
  let responders := decls.filter (isSpineFunctorResponder env ·)
  let ambiguous := decls.filter fun declName => (spineFunctorKindsOf env declName).size > 1
  let unclassified := decls.filter fun declName => (spineFunctorKindsOf env declName).isEmpty

  IO.println s!"[FunctorDiagnostics] module={moduleStr} namespace={namespaceStr}"
  IO.println ""
  IO.println "=== Spine Functor Taxonomy ==="
  IO.println s!"Tagged functors: {decls.size}"
  IO.println s!"Lifts: {lifts.size}"
  IO.println s!"Constructors: {constructors.size}"
  IO.println s!"Responders: {responders.size}"
  IO.println s!"Ambiguous: {ambiguous.size}"
  IO.println s!"Unclassified: {unclassified.size}"
  IO.println ""

  printGroup "--- Lifts ---" lifts
  IO.println ""
  printGroup "--- Constructors ---" constructors
  IO.println ""
  printGroup "--- Responders ---" responders
  IO.println ""
  printGroup "--- Ambiguous ---" ambiguous
  IO.println ""
  printGroup "--- Unclassified ---" unclassified

  return 0
