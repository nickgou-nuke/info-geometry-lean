import Lean
import DAG.Basic
import DAG.DeclIndex
import DAG.Hydrate
import DAG.TwoComplex
import DAG.GraphHodge
import DAG.CocycleBridge
import DAG.AnalyticBridge

/-!
# DAG.WittenIndexCommand

Interactive `#witten_index` command: compute the Witten index
(Euler characteristic) of any Lean module or declaration.

## Usage

```lean
#witten_index List.Basic       -- Euler characteristic of List.Basic
#witten_index Nat.add          -- Witten index of the Nat.add dependency cone
#witten_skeleton               -- print the theory skeleton of the current env
```

## Mathematical meaning

The Witten index χ = β₀ - β₁ + β₂ equals the number of irreducible
invariants (harmonic 0-chains minus harmonic 1-chains plus harmonic
2-chains) in the dependency graph.

For acyclic files: χ = number of connected components.
For files with cycles: χ < number of components (cycles reduce the index).
χ = 0 → perfect match between theorems and lemmas (critical point).
χ > 0 → surplus of irreducible theorems (productive theory).
χ < 0 → surplus of cycles/loops (over-constrained, potential refactor needed).
-/

open Lean Elab Command

namespace DAG.WittenIndexCommand

/-! ## The computation pipeline -/

/--
Build the declaration graph for a given namespace prefix.
Returns (Graph Name, HydratedGraph Name) for the filtered environment.
-/
def graphForPrefix (env : Environment) (nsPrefix : String) : DAG.Graph Name :=
  DAG.buildGraphFromEnv env (some nsPrefix)

/--
Compute the Witten index of a namespace:

    χ = V - E + F = number of connected components - cycles + faces

For the dependency DAG (no faces in the TwoComplex sense):
    χ = |nodes| - |edges| = number of declarations - number of deps.
-/
def wittenIndexOfPrefix (env : Environment) (nsPrefix : String) : Int :=
  let g := graphForPrefix env nsPrefix
  let V := g.nodes.size
  let E : Nat := (g.forward.map (fun adj => adj.size)).foldl (init := 0) (fun acc n => acc + n)
  (V : Int) - (E : Int)

/-! ## The `#witten_index` command -/

/--
`#witten_index <ident>` — compute the Witten index of a declaration's
dependency cone (backward and forward).

Uses `DeclDepIndex` from `DAG.DeclIndex` to build the bounded dependency
cone around the given declaration, then computes χ = V - E.
-/
elab "#witten_index" id:ident : command => do
  let root ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let idx := DAG.DeclDepIndex.buildBoundedCone env root 4 1 500
  -- Count declarations in the cone
  let deps := idx.deps
  let mut declSet : Std.HashSet Name := {}
  declSet := declSet.insert root
  for (n, ds) in deps.toList do
    declSet := declSet.insert n
    for d in ds do
      declSet := declSet.insert d
  for (n, us) in idx.users.toList do
    declSet := declSet.insert n
    for u in us do
      declSet := declSet.insert u
  let V := declSet.size
  -- Count edges
  let mut E : Nat := 0
  for (_, ds) in idx.deps.toList do
    E := E + ds.size
  let χ := (V : Int) - (E : Int)
  let b0 : Int := 1  -- minimal estimate: at least 1 connected component in the cone
  let b1 : Int := (E : Int) - (V : Int) + b0
  logInfo s!"[Witten Index] {root}
  Nodes (declarations): {V}
  Edges (dependencies): {E}
  Euler characteristic χ = V - E = {χ}
  Estimated β₀ = {b0}, β₁ = {b1}
  Topological classification: {
    if χ > 0 then "productive (more declarations than deps)"
    else if χ < 0 then "over-constrained (more deps than decls — potential refactor)"
    else "critical (perfect balance)"
  }"

/-! ## The `#witten_skeleton` command -/

/--
`#witten_skeleton` — print the theory skeleton of the current environment.

Computes the Witten index for the full `InfoGeometry` namespace
(or any default namespace) and prints the harmonic dimension.
-/
elab "#witten_skeleton" : command => do
  let env ← getEnv
  let g := DAG.buildGraphFromEnv env none
  let V := g.nodes.size
  let E : Nat := (g.forward.map (fun adj => adj.size)).foldl (init := 0) (fun acc n => acc + n)
  let χ := (V : Int) - (E : Int)
  logInfo s!"[Theory Skeleton]
  Total declarations: {V}
  Total dependency edges: {E}
  Full Euler characteristic χ = V - E = {χ}
  (This is a rough estimate. Build TwoComplex and compute Laplacian
   for exact Betti numbers via `lake script run dagStatus`.)"

end DAG.WittenIndexCommand
