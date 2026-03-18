import Lean
import DAG.Functor

/-!
# scripts.DAG.Exploration.SquarePromoter

Generate a quarantined strict-square promotion report outside the checked Lean
build. Candidate theorem templates are emitted as Markdown code fences, not as
compiled declarations.

Usage:
`lake env lean --run lean/scripts/DAG/Exploration/SquarePromoter.lean [module] [namespace] [output]`

Defaults:
- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
- output: `reports/strict-square-promoter.md`
-/

open Lean
open DAG

private def defaultModule : String :=
  "InfoGeometry.Canonical.All"

private def defaultNamespace : String :=
  "InfoGeometry"

private def defaultOutput : String :=
  "reports/strict-square-promoter.md"

private def argD (args : Array String) (idx : Nat) (fallback : String) : String :=
  args.getD idx fallback

private def squareSortKey
    (square : MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo) : String :=
  let (f, g, h, k) := square
  s!"{f.decl}|{g.decl}|{h.decl}|{k.decl}"

private def sortSquares
    (squares : Array (MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo)) :
    Array (MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo) :=
  squares.qsort fun a b => squareSortKey a < squareSortKey b

private def renderSquareTemplate
    (idx : Nat) (square : MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo) : String :=
  let (f, g, h, k) := square
  let n := idx + 1
  let theoremName := s!"strict_square_candidate_{n}"
  s!"## Candidate {n}\n\n" ++
  s!"- `f`: `{f.decl}` : `{f.dom} -> {f.cod}`\n" ++
  s!"- `g`: `{g.decl}` : `{g.dom} -> {g.cod}`\n" ++
  s!"- `h`: `{h.decl}` : `{h.dom} -> {h.cod}`\n" ++
  s!"- `k`: `{k.decl}` : `{k.dom} -> {k.cod}`\n\n" ++
  "```lean\n" ++
  s!"-- theorem {theoremName}\n" ++
  s!"--   -- left path:  {h.decl} ∘ {f.decl}\n" ++
  s!"--   -- right path: {k.decl} ∘ {g.decl}\n" ++
  s!"--   -- domain head: {f.dom}\n" ++
  s!"--   -- codomain head: {h.cod}\n" ++
  "--   -- TODO: instantiate the full telescope and replace this sketch with\n" ++
  "--   -- an actual equality proof once a typed promoter is available.\n" ++
  "--   : _ := by\n" ++
  "--   sorry\n" ++
  "```\n"

private def renderReport
    (moduleStr namespaceStr : String)
    (squares : Array (MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo)) : String :=
  let header :=
    s!"# Strict Square Promotion Report\n\n" ++
    s!"- module: `{moduleStr}`\n" ++
    s!"- namespace: `{namespaceStr}`\n" ++
    s!"- strict unary square candidates: `{squares.size}`\n\n"
  if squares.isEmpty then
    header ++
      "No strict unary commutative-square candidates were found.\n"
  else
    header ++ Id.run do
      let mut out := ""
      let mut idx := 0
      for square in sortSquares squares do
        out := out ++ renderSquareTemplate idx square
        idx := idx + 1
      out

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)

  let argv := args.toArray
  let moduleStr := argD argv 0 defaultModule
  let namespaceStr := argD argv 1 defaultNamespace
  let outputPath := argD argv 2 defaultOutput
  let moduleName := moduleStr.toName
  let namespaceName := namespaceStr.toName

  let env ← Lean.importModules #[{ module := moduleName }] {}
  let squares ← DAG.findCommutativeSquares env (some namespaceName) (strict := true)
  let report := renderReport moduleStr namespaceStr squares

  IO.FS.writeFile outputPath report
  IO.println s!"[SquarePromoter] strict square candidates: {squares.size}"
  IO.println s!"[SquarePromoter] wrote report: {outputPath}"
  return 0
