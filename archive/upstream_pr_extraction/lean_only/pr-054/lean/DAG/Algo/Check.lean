import DAG.Algo.Traversal

/-!
# DAG.Algo.Check

Small executable certificate checkers for finite adjacency algorithms.

These are intentionally Boolean checkers over `DAG.Algo.Adj`.  Heavier search
or export layers may produce candidate artifacts, but command/report tooling can
route them through these compact validators.
-/

namespace DAG.Algo

/-- Every adjacency target is in bounds. -/
def checkAdjBounds (adj : Adj) : Bool :=
  Id.run do
    for u in [:adj.size] do
      for v in adj[u]! do
        if !(v < adj.size) then
          return false
    return true

/-- `rev` is exactly the reverse adjacency of `adj`. -/
def checkReverseAdj (adj rev : Adj) : Bool :=
  rev == reverseAdj adj

private def parentEdgeOk (adj : Adj) (parent : Array (Option Nat)) (v : Nat) : Bool :=
  match parent[v]? with
  | none => true
  | some none => true
  | some (some u) =>
      match adj[u]? with
      | none => false
      | some nbrs => nbrs.contains v

/--
Check the local shape of a BFS parent tree:

* parent array has graph size;
* source has no parent;
* every parent edge is a real graph edge.

This is a lightweight structural checker, not a full shortest-distance proof.
-/
def checkBfsParents (adj : Adj) (src : Nat) (parent : Array (Option Nat)) : Bool :=
  Id.run do
    if parent.size != adj.size then
      return false
    if src < parent.size && parent[src]! != none then
      return false
    for v in [:parent.size] do
      if !parentEdgeOk adj parent v then
        return false
    return true

/-- Check that `order` is a topological order for `adj`. -/
def checkTopoOrder (adj : Adj) (order : Array Nat) : Bool :=
  Id.run do
    if order.size != adj.size then
      return false
    let mut seen : Array Bool := Array.replicate adj.size false
    let mut pos : Array Nat := Array.replicate adj.size 0
    for i in [:order.size] do
      let v := order[i]!
      if !(v < adj.size) || seen[v]! then
        return false
      seen := seen.set! v true
      pos := pos.set! v i
    for u in [:adj.size] do
      for v in adj[u]! do
        if !(v < adj.size) || !(pos[u]! < pos[v]!) then
          return false
    return true

end DAG.Algo
