import Lean
import InfoGeometry.Meta.EpistemicCompilerChain


/-!
# Typed Archetype Search
**QMS Note: METAPROGRAMMING INFRASTRUCTURE ONLY.**
This file provides a Lean 4 compiler macro (`#search_typed_archetypes`) to query the environment. It is pure tooling without mathematical substance.
-/
namespace InfoGeometry.MetaCompiler.Search

open Lean Meta Elab Command

/-- Search the entire Lean environment exhaustively for any declaration
    whose type is an instance of `TypedArchetype`.
    This avoids shallow string heuristics and uses kernel-level type inspection. -/
def findTypedArchetypes : MetaM (Array Name) := do
  let env ← getEnv
  let mut results := #[]
  for (name, cinfo) in env.constants do
    let type := cinfo.type
    -- We want to see if the type is an application of `TypedArchetype`
    -- Since `TypedArchetype` takes `Input : Type*`, its type is `TypedArchetype Input`
    if type.isAppOf ``InfoGeometry.MetaCompiler.TypedArchetype then
      results := results.push name
    else
      let fn := type.getAppFn
      if fn.isConstOf ``InfoGeometry.MetaCompiler.TypedArchetype then
        results := results.push name
  return results

elab "#search_typed_archetypes" : command => do
  Command.liftTermElabM do
    let archetypes ← findTypedArchetypes
    if archetypes.isEmpty then
      logInfo m!"No TypedArchetypes found in the environment."
    else
      logInfo m!"Found {archetypes.size} TypedArchetypes:"
      for arch in archetypes do
        logInfo m!"- {arch}"

end InfoGeometry.MetaCompiler.Search

#search_typed_archetypes
