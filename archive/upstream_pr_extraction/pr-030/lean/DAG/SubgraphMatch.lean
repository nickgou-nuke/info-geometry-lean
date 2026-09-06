import Lean
import DAG.Basic
import DAG.ExactMorphism

/-!
# Subgraph Pattern Matching (VF2-lite)

Implements exact subgraph homomorphism search for detecting categorical
motifs (commutative squares, spans, cospans, diamonds) in the declaration DAG.

## Algorithm

Uses a backtracking constraint-propagation search (VF2-lite) that finds all
structure-preserving maps from a small `MotifGraph` pattern into the
declaration DAG. Each candidate match is optionally verified via `isDefEq`
commutativity to confirm it is an exact categorical diagram.
-/

open Lean Meta

namespace DAG

/-! ### Motif graph definition -/

/-- A small directed graph pattern to search for in the declaration DAG. -/
structure MotifGraph where
  /-- Number of nodes in the pattern. -/
  numNodes : Nat
  /-- Directed edges as (source, target) pairs, 0-indexed. -/
  edges : Array (Nat × Nat)
  /-- Human-readable name for the motif. -/
  name : String
  deriving Repr

namespace Motif

/-- Commutative square motif: A→B, A→C, B→D, C→D. -/
def commutativeSquare : MotifGraph :=
  { numNodes := 4
    edges := #[(0, 1), (0, 2), (1, 3), (2, 3)]
    name := "CommutativeSquare" }

/-- Span motif: A→C, B→C (pullback candidate). -/
def span : MotifGraph :=
  { numNodes := 3
    edges := #[(0, 2), (1, 2)]
    name := "Span" }

/-- Cospan motif: C→A, C→B (pushout candidate). -/
def cospan : MotifGraph :=
  { numNodes := 3
    edges := #[(2, 0), (2, 1)]
    name := "Cospan" }

/-- Diamond motif: A→B, A→C, B→D, C→D (with shared source and sink). -/
def diamond : MotifGraph :=
  { numNodes := 4
    edges := #[(0, 1), (0, 2), (1, 3), (2, 3)]
    name := "Diamond" }

/-- Triangle motif: A→B, B→C, A→C (transitive closure witness). -/
def triangle : MotifGraph :=
  { numNodes := 3
    edges := #[(0, 1), (1, 2), (0, 2)]
    name := "Triangle" }

/-- Fork motif: A→B, A→C, A→D (triple cospan). -/
def fork : MotifGraph :=
  { numNodes := 4
    edges := #[(0, 1), (0, 2), (0, 3)]
    name := "Fork" }

end Motif

/-! ### Match result -/

/-- A match maps each motif node to a declaration name in the DAG. -/
structure MotifMatch where
  motif   : MotifGraph
  mapping : Array Name   -- mapping[motif_node_idx] = decl_name
  deriving Repr

/-! ### VF2-lite search -/

/-- Adjacency structure from the declaration graph for fast neighbor lookup. -/
structure DeclAdjacency where
  names   : Array Name
  nameIdx : Std.HashMap Name Nat
  fwd     : Array (Array Nat)   -- forward adjacency lists (node idx → neighbor idxs)

/-- Build adjacency structure from the environment. -/
def buildDeclAdjacency (env : Environment) (ns? : Option Name := none) : DeclAdjacency :=
  let g := DAG.buildGraphFromEnv env (nsPrefix? := ns?.map toString)
  let fwd := g.forward.map (fun adj => adj.map (·.1))
  { names := g.nodes, nameIdx := g.nodeToIdx, fwd := fwd }

/-- Check whether edge `(u, v)` exists in the adjacency. -/
def DeclAdjacency.hasEdge (adj : DeclAdjacency) (u v : Nat) : Bool :=
  if h : u < adj.fwd.size then
    adj.fwd[u].contains v
  else
    false

/--
Core VF2-lite backtracking search.

Given a motif and an adjacency structure, find all injective maps
`motif_node → dag_node` that preserve every edge.
We use simple backtracking with forward-checking constraints.
-/
partial def findMotifMatchesCore
    (motif : MotifGraph) (adj : DeclAdjacency)
    (maxResults : Nat := 1000) :
    Array MotifMatch := Id.run do
  let n := motif.numNodes
  let dagSize := adj.names.size
  if dagSize == 0 || n == 0 then return #[]

  -- Precompute which motif edges involve each motif node as source
  let mut motifOutEdges : Array (Array Nat) := Array.replicate n #[]
  for (s, t) in motif.edges do
    motifOutEdges := motifOutEdges.modify s (·.push t)

  -- Precompute which motif edges involve each motif node as target
  let mut motifInEdges : Array (Array Nat) := Array.replicate n #[]
  for (s, t) in motif.edges do
    motifInEdges := motifInEdges.modify t (·.push s)

  -- Backtracking state
  let mut results : Array MotifMatch := #[]
  let mut mapping : Array (Option Nat) := Array.replicate n none
  let mut used : Std.HashSet Nat := {}

  -- Stack-based DFS for backtracking (avoid deep recursion)
  -- Each stack frame: (motifNode, dagNodeCandidateIdx, dagCandidates)
  let mut stack : Array (Nat × Nat × Array Nat) := #[]

  -- Compute candidates for motif node 0
  let candidates0 := Array.range dagSize
  stack := stack.push (0, 0, candidates0)

  while stack.size > 0 do
    if results.size >= maxResults then break

    let top := stack[stack.size - 1]!
    let (motifNode, candIdx, candidates) := top

    if candIdx >= candidates.size then
      -- Exhausted candidates at this level — backtrack
      stack := stack.pop
      -- Undo the assignment for this motif node
      if let some prevDag := mapping[motifNode]! then
        used := used.erase prevDag
        mapping := mapping.set! motifNode none
      continue

    -- Advance candidate pointer
    stack := stack.set! (stack.size - 1) (motifNode, candIdx + 1, candidates)

    let dagNode := candidates[candIdx]!

    -- Injectivity check
    if used.contains dagNode then continue

    -- Forward constraint check: all already-mapped edges must be satisfied
    let mut edgesOk := true

    -- Check outgoing edges from motifNode to already-mapped targets
    for tgt in motifOutEdges[motifNode]! do
      if let some tgtDag := mapping[tgt]! then
        if !adj.hasEdge dagNode tgtDag then
          edgesOk := false
          break

    if !edgesOk then continue

    -- Check incoming edges from already-mapped sources to motifNode
    for src in motifInEdges[motifNode]! do
      if let some srcDag := mapping[src]! then
        if !adj.hasEdge srcDag dagNode then
          edgesOk := false
          break

    if !edgesOk then continue

    -- Assign
    -- First undo any previous assignment at this node
    if let some prevDag := mapping[motifNode]! then
      used := used.erase prevDag
    mapping := mapping.set! motifNode (some dagNode)
    used := used.insert dagNode

    if motifNode + 1 == n then
      -- Complete match found
      let matchNames := mapping.map fun
        | some idx => adj.names[idx]!
        | none => Name.anonymous
      results := results.push { motif, mapping := matchNames }
      -- Undo to continue searching
      used := used.erase dagNode
      mapping := mapping.set! motifNode none
    else
      -- Push next level with filtered candidates
      let nextMotifNode := motifNode + 1
      -- Filter candidates based on edge constraints from already-mapped nodes
      let mut nextCandidates := #[]
      for dagIdx in [:dagSize] do
        if used.contains dagIdx then continue
        -- Check all edges between nextMotifNode and already-mapped nodes
        let mut ok := true
        for tgt in motifOutEdges[nextMotifNode]! do
          if let some tgtDag := mapping[tgt]! then
            if !adj.hasEdge dagIdx tgtDag then
              ok := false
              break
        if ok then
          for src in motifInEdges[nextMotifNode]! do
            if let some srcDag := mapping[src]! then
              if !adj.hasEdge srcDag dagIdx then
                ok := false
                break
        if ok then
          nextCandidates := nextCandidates.push dagIdx
      stack := stack.push (nextMotifNode, 0, nextCandidates)

  return results

/--
Find all instances of a motif pattern in the declaration DAG.

This is the main entry point for subgraph pattern matching.
-/
def findMotifMatches
    (env : Environment) (motif : MotifGraph)
    (ns? : Option Name := none)
    (maxResults : Nat := 1000) :
    Array MotifMatch :=
  let adj := buildDeclAdjacency env ns?
  findMotifMatchesCore motif adj maxResults

/-- Print motif match results. -/
def printMotifMatches (results : Array MotifMatch) : IO Unit := do
  IO.println s!"━━━ Motif: {results[0]?.map (·.motif.name) |>.getD "?"} ━━━"
  IO.println s!"  Found {results.size} matches"
  for m in results.take 20 do
    let names := m.mapping.map toString
    IO.println s!"  {names}"
  if results.size > 20 then
    IO.println s!"  ... ({results.size - 20} more)"

end DAG
