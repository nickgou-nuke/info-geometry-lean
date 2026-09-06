import Lean
import DAG.Basic
import DAG.Disassembler
import DAG.Isomorphism
import DAG.QueryEngine
import InfoGeometry.Canonical.SpineAttributes

open Lean
open DAG

namespace DAG

/--
  Optimized Categorical Shape Search.
  Instead of O(N^4) nested loops, we use Hash Joins for O(N^2) or better.

  **DEPRECATED**: This module uses WL hashing for commutativity checks.
  Prefer `DAG.ExactMorphism` which uses exact `isDefEq` verification.
-/

structure MorphismInfo where
  decl : Name
  dom  : Name
  cod  : Name
  deriving BEq, Hashable, Repr

/--
Pure extraction of direct unary-arrow signatures after skipping leading implicit
and instance binders. This keeps authority separate from extraction, while still
harvesting declarations such as `X.toY` that are parameterized over universes
and typeclasses before their principal object argument.
-/
partial def extractDirectMorphismSignature (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .forallE _ d b bi =>
      if bi.isExplicit then
        if !(b.hasLooseBVar 0) then some (d, b) else none
      else
        extractDirectMorphismSignature b
  | _ => none

/-- Conservative extraction of named morphism-family signatures. -/
def extractNamedMorphismSignature (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConst && args.size >= 2 then
    let s := fn.constName!.toString
    if s.endsWith "Hom" || s.endsWith "Equiv" || s.endsWith "Iso" || s.endsWith "Map" then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else none
  else none

/-- Pure structural extraction of domain/codomain without authority semantics. -/
def extractMorphismSignature (e : Expr) : Option (Expr × Expr) :=
  extractDirectMorphismSignature e <|> extractNamedMorphismSignature e

/-- Legacy heuristic recognizer retained for discovery mode. -/
def recognizeMorphismShallow (e : Expr) : Option (Expr × Expr) :=
  extractMorphismSignature e

private def isHeuristicMorphismName (declName : Name) : Bool :=
  let s := declName.toString
  s.endsWith "Hom" || s.endsWith "Equiv" || s.endsWith "Iso" || s.endsWith "Map"

private def mkCanonicalMorphismInfo? (declName : Name) (e : Expr) : Option MorphismInfo := do
  let (dom, cod) ← extractMorphismSignature e
  match dom.getAppFn, cod.getAppFn with
  | .const d _ , .const c _ =>
      some { decl := declName, dom := d, cod := c }
  | _, _ =>
      none

private def mkHeuristicMorphismInfo? (declName : Name) (e : Expr) : Option MorphismInfo := do
  if !(isHeuristicMorphismName declName) && (extractNamedMorphismSignature e).isNone then
    none
  else
    mkCanonicalMorphismInfo? declName e

structure MorphismHarvest where
  tagged        : Array MorphismInfo
  heuristicName : Array MorphismInfo
  deriving Repr

def getAllMorphismsWithDiagnostics (env : Environment) (ns? : Option Name := none) :
    IO MorphismHarvest := do
  let mut canonical := #[]
  let mut heuristicOnly := #[]
  for (name, ci) in env.constants do
    if let some ns := ns? then
      if !ns.isPrefixOf name then continue
    let isTagged := InfoGeometry.Canonical.isSpineMorphism env name
    if isTagged then
      match mkCanonicalMorphismInfo? name ci.type with
      | some info =>
          canonical := canonical.push info
      | none =>
          pure ()
    else
      match mkHeuristicMorphismInfo? name ci.type with
      | some info =>
          heuristicOnly := heuristicOnly.push info
      | none =>
          pure ()
  return { tagged := canonical, heuristicName := heuristicOnly }

/--
Get all morphisms. Prefer `DAG.harvestExactMorphisms` from `ExactMorphism.lean`
for kernel-trusted extraction.
-/
def getAllMorphisms (env : Environment) (ns? : Option Name := none) (strict : Bool := true) :
    IO (Array MorphismInfo) := do
  let harvest ← getAllMorphismsWithDiagnostics env ns?
  if strict then
    return harvest.tagged
  else
    return harvest.tagged ++ harvest.heuristicName

/--
**DEPRECATED**: Uses WL structural hashing for commutativity, which can produce
false positives (hash collisions) and false negatives (syntactic variations).
Prefer `DAG.findCommutativeSquaresExact` from `ExactMorphism.lean` which uses
exact `isDefEq` kernel verification.
-/
def findCommutativeSquares (env : Environment) (ns? : Option Name := none) (strict : Bool := true) :
    IO (Array (MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo)) := do
  let morphs ← getAllMorphisms env ns? (strict := strict)
  let mut byDom : Std.HashMap Name (Array MorphismInfo) := {}
  for m in morphs do
    byDom := byDom.insert m.dom (byDom.getD m.dom #[] |>.push m)

  let mut results := #[]

  -- Iterate through pairs starting at the same node A
  for f in morphs do
    let A := f.dom
    let B := f.cod

    -- Look for g: A -> C
    if let some g_candidates := byDom.get? A then
      for g in g_candidates do
        if f.decl == g.decl then continue -- Avoid triviality
        let C := g.cod

        -- Look for h: B -> D
        if let some h_candidates := byDom.get? B then
          for h in h_candidates do
            let D := h.cod

            -- Look for k: C -> D
            if let some k_candidates := byDom.get? C then
              for k in k_candidates do
                if k.cod != D then continue
                if h.decl == k.decl then continue

                -- The Commutativity Test
                let h_of_f := Expr.lam `x (Expr.const A [])
                  (Expr.app (Expr.const h.decl []) (Expr.app (Expr.const f.decl []) (Expr.bvar 0))) .default
                let k_of_g := Expr.lam `x (Expr.const A [])
                  (Expr.app (Expr.const k.decl []) (Expr.app (Expr.const g.decl []) (Expr.bvar 0))) .default

                let hash1 := computeStructuralHash h_of_f (k := 5) (blindConstants := false)
                let hash2 := computeStructuralHash k_of_g (k := 5) (blindConstants := false)

                if hash1 == hash2 then
                  results := results.push (f, g, h, k)

  return results

end DAG
