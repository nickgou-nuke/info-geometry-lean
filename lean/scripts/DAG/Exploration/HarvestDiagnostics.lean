import Lean
import DAG.Functor

/-!
# scripts.DAG.Exploration.HarvestDiagnostics

Coverage-gap diagnostic for canonical spine morphism harvesting.

Usage:
`lake env lean --run lean/scripts/DAG/Exploration/HarvestDiagnostics.lean [module] [namespace] [limit]`

Defaults:
- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
- limit: `20`
-/

open Lean
open DAG

private def defaultModule : String :=
  "InfoGeometry.Canonical.All"

private def defaultNamespace : String :=
  "InfoGeometry"

private def defaultLimit : Nat :=
  20

private def argD (args : Array String) (idx : Nat) (fallback : String) : String :=
  args.getD idx fallback

private def parseLimit (args : Array String) : Nat :=
  match args[2]? with
  | some raw =>
      match String.toNat? raw with
      | some n => n
      | none => defaultLimit
  | none => defaultLimit

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => a.toString < b.toString

private def sortMorphisms (morphs : Array MorphismInfo) : Array MorphismInfo :=
  morphs.qsort fun a b => a.decl.toString < b.decl.toString

private def namespaceStem (declName : Name) : String :=
  match declName.toString.splitOn "." with
  | a :: b :: _ => s!"{a}.{b}"
  | [a] => a
  | _ => "<anonymous>"

private def spineMorphismDecls (env : Environment) (ns? : Option Name := none) : Array Name :=
  sortNames <| env.constants.fold (init := #[]) fun acc declName _ =>
    if let some ns := ns? then
      if !ns.isPrefixOf declName then
        acc
      else if InfoGeometry.Canonical.isSpineMorphism env declName then
        acc.push declName
      else
        acc
    else if InfoGeometry.Canonical.isSpineMorphism env declName then
      acc.push declName
    else
      acc

private def heuristicStemHistogram (morphs : Array MorphismInfo) : Array (String × Nat) :=
  Id.run do
    let mut counts : Std.HashMap String Nat := {}
    for info in morphs do
      let stem := namespaceStem info.decl
      counts := counts.insert stem (counts.getD stem 0 + 1)
    counts.toList.toArray |>.qsort fun a b =>
      if a.2 == b.2 then a.1 < b.1 else a.2 > b.2

private def printTopNames (title : String) (names : Array Name) (limit : Nat) : IO Unit := do
  if names.isEmpty then
    pure ()
  else
    IO.println title
    for declName in names[:limit] do
      IO.println s!"  {declName}"

private def printTopMorphisms (title : String) (morphs : Array MorphismInfo) (limit : Nat) : IO Unit := do
  if morphs.isEmpty then
    pure ()
  else
    IO.println title
    for info in morphs[:limit] do
      IO.println s!"  {info.decl} : {info.dom} -> {info.cod} [{namespaceStem info.decl}]"

private def printStemHistogram (histogram : Array (String × Nat)) (limit : Nat) : IO Unit := do
  if histogram.isEmpty then
    pure ()
  else
    IO.println "--- Heuristic Namespace Histogram ---"
    for (stem, count) in histogram[:limit] do
      IO.println s!"  {stem}: {count}"

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)

  let argv := args.toArray
  let moduleStr := argD argv 0 defaultModule
  let namespaceStr := argD argv 1 defaultNamespace
  let limit := parseLimit argv
  let moduleName := moduleStr.toName
  let namespaceName := namespaceStr.toName

  IO.println s!"[HarvestDiagnostics] module={moduleStr} namespace={namespaceStr} limit={limit}"

  let env ← Lean.importModules #[{ module := moduleName }] {}
  let taggedDecls := spineMorphismDecls env (some namespaceName)
  let harvest ← DAG.getAllMorphismsWithDiagnostics env (some namespaceName)
  let canonical := sortMorphisms harvest.canonical
  let heuristicOnly := sortMorphisms harvest.heuristicOnly
  let mut canonicalSet : Std.HashSet Name := {}
  for info in canonical do
    canonicalSet := canonicalSet.insert info.decl
  let unharvested := taggedDecls.filter fun declName => !(canonicalSet.contains declName)
  let histogram := heuristicStemHistogram heuristicOnly

  IO.println ""
  IO.println "=== Morphism Harvest Report ==="
  IO.println s!"Tagged spine morphisms: {taggedDecls.size}"
  IO.println s!"Canonical harvested morphisms: {canonical.size}"
  IO.println s!"Tagged but unharvested: {unharvested.size}"
  IO.println s!"Heuristic-only extras: {heuristicOnly.size}"

  IO.println ""
  printTopNames "--- Tagged But Unharvested ---" unharvested limit
  if unharvested.isEmpty then
    IO.println "--- Tagged But Unharvested ---"
    IO.println "  <none>"

  IO.println ""
  printStemHistogram histogram limit

  IO.println ""
  printTopMorphisms "--- Heuristic-Only Extras ---" heuristicOnly limit
  if heuristicOnly.isEmpty then
    IO.println "--- Heuristic-Only Extras ---"
    IO.println "  <none>"

  return 0
