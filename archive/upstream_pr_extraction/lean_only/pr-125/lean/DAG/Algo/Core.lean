import Std
import DAG.Basic

/-!
# DAG.Algo.Core

Small indexed adjacency primitives for reusable graph algorithms.

This layer intentionally knows nothing about Lean `Environment` or declaration
names.  It operates on finite indexed adjacency arrays.
-/

namespace DAG.Algo

/-- Finite unweighted adjacency array. -/
abbrev Adj := Array (Array Nat)

/-- Drop edge-kind labels from a `DAG.Graph`. -/
def stripKinds {α} [BEq α] [Hashable α] (g : DAG.Graph α) : Adj :=
  g.forward.map (fun es => es.map (fun e => e.1))

/-- Reverse adjacency. -/
def reverseAdj (adj : Adj) : Adj :=
  Id.run do
    let mut rev : Adj := Array.replicate adj.size #[]
    for u in [:adj.size] do
      for v in adj[u]! do
        if v < rev.size then
          rev := rev.modify v (fun xs => xs.push u)
    rev

/-- Out-degree of a vertex, with out-of-range vertices treated as isolated. -/
def outDegree (adj : Adj) (u : Nat) : Nat :=
  match adj[u]? with
  | some xs => xs.size
  | none => 0

/-- In-degrees for all vertices. -/
def inDegrees (adj : Adj) : Array Nat :=
  Id.run do
    let mut deg := Array.replicate adj.size 0
    for u in [:adj.size] do
      for v in adj[u]! do
        if v < deg.size then
          deg := deg.modify v (fun x => x + 1)
    deg

/-- Total number of directed edges. -/
def edgeCount (adj : Adj) : Nat :=
  adj.foldl (fun s xs => s + xs.size) 0

end DAG.Algo
