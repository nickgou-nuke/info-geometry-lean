import Lean
import DAG.Functor
import InfoGeometry.Canonical.All
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.Functor

Exploratory script for canonical morphism-harvest diagnostics and strict
commutative-square search over the InfoGeometry spine.
-/

open Lean
open DAG

private def imports : Array Import := #[
  { module := `DAG.Functor },
  { module := `InfoGeometry.Canonical.All }
]

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => a.toString < b.toString

private def sortMorphisms (morphs : Array MorphismInfo) : Array MorphismInfo :=
  morphs.qsort fun a b => a.decl.toString < b.decl.toString

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

private def namespaceLabel (ns? : Option Name) : String :=
  match ns? with
  | some ns => ns.toString
  | none => "<all>"

private def printHarvestDiagnostics (env : Environment) (ns? : Option Name := none) : IO Unit := do
  let taggedDecls := spineMorphismDecls env ns?
  let harvest ← DAG.getAllMorphismsWithDiagnostics env ns?
  let canonical := sortMorphisms harvest.canonical
  let heuristicOnly := sortMorphisms harvest.heuristicOnly
  let mut canonicalSet : Std.HashSet Name := {}
  for info in canonical do
    canonicalSet := canonicalSet.insert info.decl
  let unharvested := taggedDecls.filter fun declName => !(canonicalSet.contains declName)

  IO.println s!"--- Morphism Harvest Diagnostics ({namespaceLabel ns?}) ---"
  IO.println s!"Tagged spine morphisms: {taggedDecls.size}"
  IO.println s!"Harvested canonical morphisms: {canonical.size}"
  IO.println s!"Unharvested tagged morphisms: {unharvested.size}"
  IO.println s!"Heuristic-only extras: {heuristicOnly.size}"

  if !unharvested.isEmpty then
    IO.println "Tagged but not harvested:"
    for declName in unharvested[:10] do
      IO.println s!"  {declName}"

  if !heuristicOnly.isEmpty then
    IO.println "Heuristic-only extras:"
    for info in heuristicOnly[:10] do
      IO.println s!"  {info.decl} : {info.dom} -> {info.cod}"

private def runFunctor (env : Environment) : IO Unit := do
  let ns := some `InfoGeometry
  printHarvestDiagnostics env ns
  IO.println ""
  IO.println s!"--- Strict Commutative Square Search ({namespaceLabel ns}) ---"
  let squares ← DAG.findCommutativeSquares env ns

  if squares.isEmpty then
    IO.println "No commutative squares found."
  else
    IO.println s!"Found {squares.size} Commutative Squares!"
    for (f, g, h, k) in squares[:5] do
      IO.println s!"Square: ({f.decl}, {g.decl}, {h.decl}, {k.decl})"

def main : IO Unit :=
  ScriptDAGExploration.runEnvScript imports runFunctor
