import Lean
import DAG.Basic
import DAG.Disassembler
import DAG.TwoComplex
import DAG.Hydrate

open Lean

namespace DAG

/--
  The Homology Engine.
  It takes a raw Lambda AST (Expr) and computes its topological invariants.
-/
def computeExprHomology (e : Expr) : MetaM Unit := do
  -- 1. Disassemble the Expr into a Graph
  let exprGraph := disassembleExpr e

  -- 2. Convert ExprGraph to our standard Graph Nat (using IDs)
  let n := exprGraph.nodes.size
  let mut forward : Array (Array (Nat × EdgeKind)) := Array.replicate n #[]
  for edge in exprGraph.edges do
    let kind := match edge.role with
      | "type" => EdgeKind.type
      | _      => EdgeKind.value
    forward := forward.modify edge.source (fun arr => arr.push (edge.target, kind))

  let g : Graph Nat := {
    nodes := (Array.range n),
    nodeToIdx := (Array.range n).foldl (init := {}) (fun acc i => acc.insert i i),
    forward := forward
  }

  -- 3. Use the canonical hydration owner for SCCs, predecessors,
  --    topological order, and dominators.
  let h : HydratedGraph Nat := hydrate g

  -- 4. Build the 2-Complex
  let tc := buildTwoComplex h

  -- 5. Calculate Invariants
  let chi := eulerCharacteristic tc
  let b1 := betti1 tc

  IO.println s!"--- Topological Analysis ---"
  IO.println s!"Nodes (V): {n}"
  IO.println s!"Edges (E): {tc.edges.size}"
  IO.println s!"Faces (F): {tc.faces.size} (Commutative Triangles)"
  IO.println s!"Euler Characteristic (χ): {chi}"
  IO.println s!"First Betti Number (b₁): {b1} (Independent Loops)"

  if b1 > 0 then
    IO.println s!"Found {b1} structural knots in the logic."
  else
    IO.println "The logic is topologically simple (a tree-like DAG)."

end DAG
