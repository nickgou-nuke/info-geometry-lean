import DAG.Algo.Core

/-!
# DAG.Algo.Traversal

Reusable BFS traversal routines over finite indexed adjacency arrays.
-/

namespace DAG.Algo

/-- Unweighted BFS distances from `src`. Unreachable vertices are `none`. -/
def bfsDistances (adj : Adj) (src : Nat) : Array (Option Nat) :=
  Id.run do
    let mut dist : Array (Option Nat) := Array.replicate adj.size none

    if src < adj.size then
      dist := dist.set! src (some 0)

      let mut q : Array Nat := #[src]
      let mut head : Nat := 0

      while head < q.size do
        let u := q[head]!
        head := head + 1

        let some du := dist[u]! | continue

        for v in adj[u]! do
          if v < adj.size && dist[v]!.isNone then
            dist := dist.set! v (some (du + 1))
            q := q.push v

    dist

/-- Reachability mask from `src`. -/
def reachableFrom (adj : Adj) (src : Nat) : Array Bool :=
  (bfsDistances adj src).map Option.isSome

/-- BFS tree parent array from `src`. The source and unreachable vertices have no parent. -/
def bfsTreeParents (adj : Adj) (src : Nat) : Array (Option Nat) :=
  Id.run do
    let mut parent : Array (Option Nat) := Array.replicate adj.size none
    let mut seen : Array Bool := Array.replicate adj.size false

    if src < adj.size then
      seen := seen.set! src true
      let mut q : Array Nat := #[src]
      let mut head : Nat := 0

      while head < q.size do
        let u := q[head]!
        head := head + 1

        for v in adj[u]! do
          if v < adj.size && !seen[v]! then
            seen := seen.set! v true
            parent := parent.set! v (some u)
            q := q.push v

    parent

end DAG.Algo
