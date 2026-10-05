# Epistemic Metaprogramming & Typed Archetypes in Lean 4

## 1. What We Have in Category, Meta, and DAG Lanes
Based on an exhaustive environment and tree trace, here is the state of Directed Homotopy, DAG Categories, and Typed Archetypes:

**Meta Lane (`InfoGeometry/Meta/`)**
- **The Core Owner**: `lean/InfoGeometry/Meta/EpistemicCompilerChain.lean` defines `TypedArchetype Input`, a strongly-typed structure linking a theorem schema (`Input → Prop`) to the 6-stage epistemic causal pipeline (`Phase`) and its verification state (`Status`).
- **The Evidence Gate**: A `TypedArchetype` holds a function `evidence : ∀ input, status = Status.proved → claim input`. The evidence is structurally inaccessible unless the compiler verifies `status = Status.proved`. We natively formalized the `discharge` function to safely extract these proofs once promoted.
- **The Search Metaprogram**: I implemented `lean/InfoGeometry/Meta/TypedArchetypeSearch.lean`, which scans the `Lean.Environment` explicitly for `isAppOf ``TypedArchetype`. This is a deep kernel-level type inspection, not a shallow string heuristic.

**Topology / Category / DAG Lanes**
- **Directed Homotopy**: `lean/InfoGeometry/Topology/ChiralDirectedGraphHomotopy.lean` defines `DirectedChiralHomotopyEquiv` and `ChiralPathCategory`, forming a strict 1-category from raw directed paths.
- **DAG Categories**: `lean/InfoGeometry/Causal/ProofDAGRepresentation.lean`, `lean/InfoGeometry/Canonical/DAGCategoryWheelerUnificationBridge.lean`, and `lean/InfoGeometry/MassSpectrometry/FragmentationDAG.lean` formalize directed acyclic graphs directly as small categories, turning edges into morphisms.

## 2. Formalizing Archetypes in Metaprogramming
In Lean 4, metaprogramming allows us to reflect over the kernel environment and manipulate these structures dynamically. An archetype is **not just a string or an enum** (as previously seen in `MetaEpistemicCompiler.lean`'s string-based registry), but a **parameterized mathematical blueprint** injected into the `MetaM` monad.

Here is how we formally implemented the deep exhaustive search in Lean 4:

```lean
import Lean
import InfoGeometry.Meta.EpistemicCompilerChain

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
    -- Deep type inspection against the kernel registry:
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
```

## 3. Epistemic Purpose
Epistemically, a `TypedArchetype` serves as a **safe forward-declaration** for the AI agents (the "Epistemic Compiler"). 
1. **Schema Formulation**: An agent spots a pattern (e.g., "all parallel paths in this chiral DAG are directed-homotopic"). 
2. **Phase Injection**: It creates a `TypedArchetype` with `status := Status.speculative` and `claim := (the theorem schema)`. 
3. **Quarantine**: The kernel knows the *statement* exists, but the `evidence` field requires `status = proved`. No downstream code can accidentally use a hallucinated proof, because `TypedArchetype.discharge` safely evaluates to `none` if the status is unproved.
4. **Resolution**: Once an agent synthesizes the proof, the status is bumped to `proved`, the evidence is supplied, and the macro extracts the `PLift` verified theorems for global repository use.

This physically enforces the repository's Zero-Gap policy directly in the Lean 4 type system, rather than relying on external Python scripts or unverified string tags.
