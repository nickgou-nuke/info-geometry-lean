import Lean
import DAG.LiftNaturality

/-!
# scripts.DAG.Exploration.LiftNaturalityDiagnostics

Report-only matcher for proved equality theorems that mention the tagged
`@[spine_functor_lift]` surface.

Usage:
`lake env lean --run lean/scripts/DAG/Exploration/LiftNaturalityDiagnostics.lean [module] [namespace] [output]`

Defaults:
- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
- output: `reports/lift-naturality-diagnostics.md`
-/

open Lean
open DAG

private def defaultModule : String :=
  "InfoGeometry.Canonical.All"

private def defaultNamespace : String :=
  "InfoGeometry"

private def defaultOutput : String :=
  "reports/lift-naturality-diagnostics.md"

private def argD (args : Array String) (idx : Nat) (fallback : String) : String :=
  args.getD idx fallback

private def renderLiftNames (names : Array Name) : String :=
  if names.isEmpty then
    "[]"
  else
    "[" ++ String.intercalate ", " ((names.map fun n => s!"`{n}`").toList) ++ "]"

private def renderSeed (seed : LiftSeed) : String :=
  let normalizationNote :=
    match seed.normalizationError? with
    | some err => s!"- normalization error: `{err}`\n\n"
    | none => "\n"
  s!"## `{seed.theoremName}`\n\n" ++
    s!"- head lift mentions: {renderLiftNames seed.headLiftMentions}\n" ++
    s!"- lift mentions: {renderLiftNames seed.liftMentions}\n" ++
    s!"- raw hash match: `{seed.rawHashEq}`\n" ++
    s!"- normalized hash match: `{seed.normHashEq}`\n" ++
    s!"- normalized defeq: `{seed.normDefEq}`\n" ++
    normalizationNote ++
    "### Raw sides\n\n" ++
    "```lean\n" ++
    s!"lhs := {seed.rawLhs}\n" ++
    s!"rhs := {seed.rawRhs}\n" ++
    "```\n\n" ++
    "### Normalized sides\n\n" ++
    "```lean\n" ++
    s!"lhs := {seed.normLhs}\n" ++
    s!"rhs := {seed.normRhs}\n" ++
    "```\n\n"

private def renderReport (moduleStr namespaceStr : String) (lifts : Array Name) (seeds : Array LiftSeed) : String :=
  let normalizedDefEqCount := seeds.foldl (init := 0) fun acc seed => acc + if seed.normDefEq then 1 else 0
  let header :=
    s!"# Lift Naturality Diagnostics\n\n" ++
    s!"- module: `{moduleStr}`\n" ++
    s!"- namespace: `{namespaceStr}`\n" ++
    s!"- tagged lift functors: `{lifts.size}`\n" ++
    s!"- matched equality theorems: `{seeds.size}`\n" ++
    s!"- normalized defeq seeds: `{normalizedDefEqCount}`\n\n" ++
    "Tagged lift functors:\n\n" ++
    String.join ((lifts.map fun n => s!"- `{n}`\n").toList) ++ "\n"
  if seeds.isEmpty then
    header ++ "No proved equality theorems mentioning tagged lift functors were found.\n"
  else
    header ++ String.join ((seeds.map renderSeed).toList)

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)

  let argv := args.toArray
  let moduleStr := argD argv 0 defaultModule
  let namespaceStr := argD argv 1 defaultNamespace
  let outputPath := argD argv 2 defaultOutput
  let moduleName := moduleStr.toName
  let namespaceName := namespaceStr.toName

  let env ← Lean.importModules #[{ module := moduleName }] {}
  let ctxCore : Core.Context := { fileName := "<LiftNaturalityDiagnostics>", fileMap := default }
  let sCore : Core.State := { env := env }
  let ((seeds, lifts), _) ← (collectLiftSeeds env namespaceName).toIO ctxCore sCore
  let report := renderReport moduleStr namespaceStr lifts seeds
  IO.FS.writeFile outputPath report
  IO.println s!"[LiftNaturalityDiagnostics] tagged lift functors: {lifts.size}"
  IO.println s!"[LiftNaturalityDiagnostics] matched equality theorems: {seeds.size}"
  IO.println s!"[LiftNaturalityDiagnostics] wrote report: {outputPath}"
  pure 0
