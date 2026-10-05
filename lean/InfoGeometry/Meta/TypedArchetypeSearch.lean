import Lean
import InfoGeometry.Meta.EpistemicCompilerChain

/-!
# Typed Archetype Search
**QMS Note: METAPROGRAMMING INFRASTRUCTURE ONLY.**
This file provides a Lean 4 compiler macro (`#search_typed_archetypes`) to query the environment. It is pure tooling without mathematical substance.
-/

namespace InfoGeometry.MetaCompiler.Search

open Lean Meta Elab Command

/-- Exhaustive search that handles polymorphism, type aliases, and universe levels. -/
def findTypedArchetypes : MetaM (Array (Name × ConstantInfo)) := do
  let env ← getEnv
  let mut results := #[]
  for (declName, cinfo) in env.constants do
    if !declName.isInternal then
      let isArchetype ← forallTelescopeReducing cinfo.type fun _ body => do
        let body ← whnf body
        return body.isAppOf ``InfoGeometry.MetaCompiler.TypedArchetype
      if isArchetype then
        results := results.push (declName, cinfo)
  return results

def auditArchetypeSoundness (declName : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? declName with
  | none => throwError "Declaration {declName} not found."
  | some _ => do
    let axioms ← Lean.collectAxioms declName
    let axiomList := axioms.toList
    if axiomList.contains ``sorryAx then
      throwError "REJECTED: Archetype {declName} relies on 'sorry'."
    return axiomList

elab "#search_typed_archetypes" : command => do
  Command.liftTermElabM do
    let archetypes ← findTypedArchetypes
    if archetypes.isEmpty then
      logInfo m!"No TypedArchetypes found in the environment."
    else
      logInfo m!"Found {archetypes.size} TypedArchetypes:"
      for (arch, _) in archetypes do
        logInfo m!"- {arch}"

end InfoGeometry.MetaCompiler.Search
