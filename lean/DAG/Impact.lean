

import Std.Data.HashMap
import Std.Data.HashSet
import DAG.Basic

namespace DAG

def impact {α} [BEq α] [Hashable α] [Inhabited α]
  (g : HydratedGraph α) (n : α) : Array α :=
  Id.run do
    let some u := g.toGraph.nodeToIdx.get? n | return #[]
    let start := g.sccOf[u]!
    let mut seen : Std.HashSet Nat := Std.HashSet.ofList []
    let mut q : List Nat := [start]
    seen := Std.HashSet.insert seen start
    while true do
      match q with
      | [] => break
      | x :: xs =>
          q := xs
          for y in g.dag[x]! do
            if !Std.HashSet.contains seen y then
              seen := Std.HashSet.insert seen y
              q := y :: q
    let mut out := #[]
    for s in Std.HashSet.toList seen do
      for v in g.sccs[s]! do
        out := out.push g.toGraph.nodes[v]!
    out

def reverseImpact {α} [BEq α] [Hashable α] [Inhabited α]
  (g : HydratedGraph α) (n : α) : Array α :=
  Id.run do
    let some u := g.toGraph.nodeToIdx.get? n | return #[]

    -- start at the SCC of n
    let start := g.sccOf[u]!

    -- visited SCCs
    let mut seen : Std.HashSet Nat := Std.HashSet.ofList []
    let mut q : List Nat := [start]

    seen := Std.HashSet.insert seen start

    -- BFS over reverse DAG
    while true do
      match q with
      | [] => break
      | x :: xs =>
          q := xs
          for p in g.preds[x]! do
            if !Std.HashSet.contains seen p then
              seen := Std.HashSet.insert seen p
              q := p :: q

    -- lift SCCs back to original nodes
    let mut out := #[]
    for s in Std.HashSet.toList seen do
      for v in g.sccs[s]! do
        out := out.push g.toGraph.nodes[v]!

    out

end DAG
