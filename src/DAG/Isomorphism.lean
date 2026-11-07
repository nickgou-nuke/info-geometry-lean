import Lean
import DAG.Basic
import DAG.Disassembler

open Lean

namespace DAG

/--
  The Weisfeiler-Lehman (WL) Isomorphism Engine.

  **Note**: For commutativity checking, prefer `DAG.ExactMorphism`
  which uses exact `isDefEq` kernel verification. WL hashing remains
  useful for structural similarity detection where exact equality
  is not the question.
-/

def computeInitialLabel (node : GraphNode) (blindConstants : Bool) : UInt64 :=
  let base := hash node.kind
  if node.kind == "const" && blindConstants then
    mixHash base (hash "<CONST>")
  else
    mixHash base (hash (toString node.info))

def wlRound (nodes : Array GraphNode) (edges : Array GraphEdge) (labels : Array UInt64) : Array UInt64 := Id.run do
  let n := nodes.size
  let mut newLabels := Array.replicate n (0 : UInt64)

  -- Group hashes by source
  let mut adj : Array (Array (UInt64 × UInt64)) := Array.replicate n #[]
  for edge in edges do
    let roleHash := hash edge.role
    adj := adj.modify edge.source (fun arr => arr.push (roleHash, labels[edge.target]!))

  for i in [:n] do
    let currentLabel := labels[i]!
    -- Sort neighbor hashes (role_hash ^ neighbor_label_hash) for permutation invariance
    let mut neighborHashes := adj[i]!.map (fun (r, l) => mixHash r l)
    neighborHashes := neighborHashes.qsort (· < ·)

    let mut h := currentLabel
    for nh in neighborHashes do
      h := mixHash h nh
    newLabels := newLabels.set! i h

  return newLabels

/--
Compute a WL structural hash of an expression.

**Note**: For commutativity / equality checking, prefer `isDefEq`
from `DAG.ExactMorphism`. This hash is an approximation subject to
collisions and is best used for similarity clustering, not exact proofs.
-/
def computeStructuralHash (e : Expr) (k : Nat := 5) (blindConstants : Bool := false) : UInt64 := Id.run do
  let g := disassembleExpr e
  let mut labels := g.nodes.map (fun n => computeInitialLabel n blindConstants)

  for _ in [:k] do
    labels := wlRound g.nodes g.edges labels

  return labels[0]?.getD 0

/--
Compare two declarations for structural symmetry using WL hashing.

**Note**: For exact equality, prefer `Lean.Meta.isDefEq` via
`DAG.ExactMorphism.checkCommutativityExact`.
-/
def compareSymmetry (env : Environment) (n1 n2 : Name) : IO Unit := do
  let ci1 := env.find? n1
  let ci2 := env.find? n2

  match ci1, ci2 with
  | some c1, some c2 =>
    if let (some v1, some v2) := (c1.value?, c2.value?) then
      let h1 := computeStructuralHash v1 (k := 10) (blindConstants := true)
      let h2 := computeStructuralHash v2 (k := 10) (blindConstants := true)

      IO.println s!"Comparing {n1} and {n2}..."
      IO.println s!"  Structural Hash 1: {h1}"
      IO.println s!"  Structural Hash 2: {h2}"

      if h1 == h2 then
        IO.println s!"[MATCH] {n1} and {n2} are STRUCTURALLY ISOMORPHIC (Templates match)!"
      else
        IO.println s!"[DIFF] {n1} and {n2} have different logical structures."
    else
      IO.println "One of the declarations has no value."
  | _, _ => IO.println "Declarations not found."

end DAG
