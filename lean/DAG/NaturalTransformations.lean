import DAG.Basic
import DAG.ExactMorphism
import DAG.CategoryBridge
import DAG.CategoryQuiver
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

open Lean Meta
open CategoryTheory
open DAG

namespace DAG.NaturalTransformations

/-!
# Natural Transformation Extraction

This module extracts natural transformations from theorem types in the repository.
-/

structure NaturalityCandidate where
  theoremDecl : Name
  componentPattern : Option Name
  suspectedNaturality : Bool

/--
Scan the environment for theorems that look like naturality statements.

Heuristics:
1. Theorem name contains "natural", "naturality", "transformation", "commutes"
2. Type involves function composition equality
-/
def findNaturalityCandidates (env : Environment) (ns? : Option Name := none) :
    Array NaturalityCandidate := Id.run do
  let mut candidates := #[]
  let keywords := #["natural", "naturality", "transformation", "commutes"]
  for (name, _) in env.constants do
    if let some ns := ns? then
      if !ns.isPrefixOf name then continue
    let nameStr := name.toString.toLower
    if keywords.any (fun kw => nameStr.contains kw) then
      candidates := candidates.push {
        theoremDecl := name
        componentPattern := none
        suspectedNaturality := true
      }
  return candidates

/--
Format a naturality candidate for display.
-/
def formatCandidate (c : NaturalityCandidate) : MetaM String := do
  let env ← getEnv
  let thmStr := c.theoremDecl.toString
  match env.find? c.theoremDecl with
  | some ci =>
    let typeStr := toString (← ppExpr ci.type)
    return s!"{thmStr} : {typeStr}"
  | none =>
    return s!"{thmStr} (not found in environment)"

/--
Print all naturality candidates in a namespace.
-/
def printNaturalityCandidates (ns? : Option Name := none) : MetaM Unit := do
  let env ← getEnv
  let candidates := findNaturalityCandidates env ns?
  IO.println s!"Found {candidates.size} naturality candidates:"
  for c in candidates do
    let formatted ← formatCandidate c
    IO.println s!"  {formatted}"

/-!
## Component extraction helpers
-/

/--
Try to extract the component function from a theorem type.

Looks for patterns like:
- `∀ X, η X : F X → G X`
- `∀ X, ∃ η_X, ...`

-/
private partial def firstConstant? : Expr → Option Name
  | .const name _ => some name
  | .app fn arg =>
      match firstConstant? fn with
      | some name => some name
      | none => firstConstant? arg
  | .lam _ domain body _
  | .forallE _ domain body _ =>
      match firstConstant? domain with
      | some name => some name
      | none => firstConstant? body
  | .letE _ value type body _ =>
      match firstConstant? value with
      | some name => some name
      | none =>
        match firstConstant? type with
        | some name => some name
        | none => firstConstant? body
  | .mdata _ body => firstConstant? body
  | .proj _ _ body => firstConstant? body
  | .sort _ | .bvar _ | .fvar _ | .lit _ | .mvar _ => none

def extractComponentFromType? (thmType : Expr) :
    MetaM (Option Name) := do
  let type ← whnf thmType
  match type with
  | .forallE _ _ body _ =>
      return firstConstant? body
  | _ =>
      return none

/-!
## Verification utilities
-/

/--
Count how many theorems in a namespace have naturality-like names.
-/
def countNaturalityTheorems (env : Environment) (ns? : Option Name := none) :
    MetaM ℕ := do
  let mut count := 0
  let keywords := #["natural", "naturality", "transformation", "commutes"]
  for (name, _) in env.constants do
    if let some ns := ns? then
      if !ns.isPrefixOf name then continue
    let nameStr := name.toString.toLower
    if keywords.any fun kw => nameStr.contains kw then
      count := count + 1
  return count

/--
Check if a specific theorem has a naturality-square type structure.
-/
def isNaturalitySquare? (thmDecl : Name) : MetaM Bool := do
  let env ← getEnv
  match env.find? thmDecl with
  | some ci =>
    let thmType := ci.type
    let typeStr := toString (← ppExpr thmType)
    return typeStr.contains "∘" && typeStr.contains "="
  | none =>
    return false

/-!
## Naturality diagnostics command
-/

/--
Run naturality diagnostics on a namespace.

Usage:
```lean
#eval DAG.NaturalTransformations.runDiagnostics (some `InfoGeometry)
```
-/
def runDiagnostics (ns? : Option Name := none) : MetaM Unit := do
  let env ← getEnv
  let count ← countNaturalityTheorems env ns?
  IO.println s!"\n=== Naturality Diagnostics ==="
  IO.println s!"Namespace: {ns?.getD `global}"
  IO.println s!"Theorems with naturality-like names: {count}"
  IO.println ""
  let candidates := findNaturalityCandidates env ns?
  IO.println s!"Detailed candidates ({candidates.size}):"
  for c in candidates do
    let formatted ← formatCandidate c
    IO.println s!"  {formatted}"
    let isSquare ← isNaturalitySquare? c.theoremDecl
    IO.println s!"    Has composition-equality structure: {isSquare}"
  IO.println ""

end DAG.NaturalTransformations
